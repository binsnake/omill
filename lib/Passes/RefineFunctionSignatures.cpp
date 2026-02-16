#include "omill/Passes/RefineFunctionSignatures.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

namespace omill {

namespace {

/// Classify how a function parameter is used.
enum class ParamKind {
  kInteger,      // Default — keep as i64
  kPointer,      // Dereferenced — refine to ptr
  kFloatingPoint // FP operations — refine to double
};

/// Walk uses of a parameter to determine its likely type.
ParamKind classifyParam(llvm::Argument *arg) {
  bool is_deref = false;
  bool is_fp = false;

  for (auto *U : arg->users()) {
    // inttoptr → pointer dereference
    if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(U)) {
      // Check if the inttoptr result is loaded/stored.
      for (auto *IU : ITP->users()) {
        if (llvm::isa<llvm::LoadInst>(IU) || llvm::isa<llvm::StoreInst>(IU) ||
            llvm::isa<llvm::GetElementPtrInst>(IU)) {
          is_deref = true;
        }
      }
    }

    // Floating-point operations.
    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(U)) {
      auto *callee = CI->getCalledFunction();
      if (callee) {
        llvm::StringRef name = callee->getName();
        if (name.starts_with("llvm.") &&
            (name.contains("fabs") || name.contains("sqrt") ||
             name.contains("fma") || name.contains("floor") ||
             name.contains("ceil"))) {
          is_fp = true;
        }
      }
    }

    // sitofp/uitofp: integer to FP conversion of parameter
    if (llvm::isa<llvm::SIToFPInst>(U) || llvm::isa<llvm::UIToFPInst>(U)) {
      is_fp = true;
    }

    // bitcast to double/float
    if (auto *BC = llvm::dyn_cast<llvm::BitCastInst>(U)) {
      if (BC->getType()->isFloatingPointTy()) {
        is_fp = true;
      }
    }
  }

  // Prefer pointer over FP if both detected (unlikely).
  if (is_deref) return ParamKind::kPointer;
  if (is_fp) return ParamKind::kFloatingPoint;
  return ParamKind::kInteger;
}

/// Convert ParamKind to LLVM type.
llvm::Type *kindToType(ParamKind kind, llvm::LLVMContext &Ctx) {
  switch (kind) {
    case ParamKind::kPointer:
      return llvm::PointerType::get(Ctx, 0);
    case ParamKind::kFloatingPoint:
      return llvm::Type::getDoubleTy(Ctx);
    default:
      return llvm::Type::getInt64Ty(Ctx);
  }
}

}  // namespace

llvm::PreservedAnalyses RefineFunctionSignaturesPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &Ctx = M.getContext();
  bool changed = false;

  // Collect _native functions to process.
  llvm::SmallVector<llvm::Function *, 16> to_refine;
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    if (!F.getName().ends_with("_native")) continue;
    to_refine.push_back(&F);
  }

  for (auto *F : to_refine) {
    // Classify each parameter.
    llvm::SmallVector<ParamKind, 6> kinds;
    bool needs_refinement = false;

    for (auto &arg : F->args()) {
      if (!arg.getType()->isIntegerTy(64)) {
        kinds.push_back(ParamKind::kInteger);
        continue;
      }

      auto kind = classifyParam(&arg);
      kinds.push_back(kind);
      if (kind != ParamKind::kInteger) {
        needs_refinement = true;
      }
    }

    if (!needs_refinement) continue;

    // Build new function type.
    llvm::SmallVector<llvm::Type *, 6> new_param_types;
    for (unsigned i = 0; i < F->arg_size(); ++i) {
      if (i < kinds.size() && F->getArg(i)->getType()->isIntegerTy(64)) {
        new_param_types.push_back(kindToType(kinds[i], Ctx));
      } else {
        new_param_types.push_back(F->getArg(i)->getType());
      }
    }

    auto *new_fn_ty = llvm::FunctionType::get(
        F->getReturnType(), new_param_types, F->isVarArg());

    // Create new function.
    auto *new_fn = llvm::Function::Create(
        new_fn_ty, F->getLinkage(), F->getName() + ".refined", M);
    new_fn->copyAttributesFrom(F);

    // Move basic blocks from old to new function.
    new_fn->splice(new_fn->begin(), F);

    // Remap arguments: insert conversion instructions at entry.
    auto &entry = new_fn->getEntryBlock();
    llvm::IRBuilder<> B(&*entry.getFirstInsertionPt());

    for (unsigned i = 0; i < F->arg_size(); ++i) {
      auto *old_arg = F->getArg(i);
      auto *new_arg = new_fn->getArg(i);
      new_arg->setName(old_arg->getName());

      if (old_arg->getType() == new_arg->getType()) {
        old_arg->replaceAllUsesWith(new_arg);
        continue;
      }

      // Insert conversion from refined type to i64.
      llvm::Value *converted = nullptr;
      if (kinds[i] == ParamKind::kPointer) {
        converted = B.CreatePtrToInt(new_arg, old_arg->getType());
      } else if (kinds[i] == ParamKind::kFloatingPoint) {
        converted = B.CreateBitCast(new_arg, old_arg->getType());
      }

      if (converted) {
        old_arg->replaceAllUsesWith(converted);
      } else {
        old_arg->replaceAllUsesWith(new_arg);
      }
    }

    // Update all call sites.
    llvm::SmallVector<llvm::CallInst *, 8> calls;
    for (auto *U : F->users()) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(U)) {
        calls.push_back(CI);
      }
    }

    for (auto *CI : calls) {
      llvm::IRBuilder<> CB(CI);
      llvm::SmallVector<llvm::Value *, 6> new_args;

      for (unsigned i = 0; i < CI->arg_size(); ++i) {
        auto *arg = CI->getArgOperand(i);
        if (i < kinds.size() && arg->getType()->isIntegerTy(64)) {
          if (kinds[i] == ParamKind::kPointer) {
            new_args.push_back(CB.CreateIntToPtr(arg, new_param_types[i]));
          } else if (kinds[i] == ParamKind::kFloatingPoint) {
            new_args.push_back(CB.CreateBitCast(arg, new_param_types[i]));
          } else {
            new_args.push_back(arg);
          }
        } else {
          new_args.push_back(arg);
        }
      }

      auto *new_call = CB.CreateCall(new_fn, new_args);
      new_call->setCallingConv(CI->getCallingConv());
      CI->replaceAllUsesWith(new_call);
      CI->eraseFromParent();
    }

    // Replace remaining uses (e.g., function pointer references).
    if (!F->use_empty()) {
      auto *bc = llvm::ConstantExpr::getBitCast(new_fn, F->getType());
      F->replaceAllUsesWith(bc);
    }

    // Take over the old name.
    std::string old_name = F->getName().str();
    F->eraseFromParent();
    new_fn->setName(old_name);

    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
