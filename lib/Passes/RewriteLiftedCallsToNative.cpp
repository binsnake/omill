#include "omill/Passes/RewriteLiftedCallsToNative.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

// x86-64 State struct offsets (Win64 ABI registers).
static constexpr uint64_t kRCXOffset = 2248;
static constexpr uint64_t kRDXOffset = 2264;
static constexpr uint64_t kR8Offset = 2344;
static constexpr uint64_t kR9Offset = 2360;
static constexpr uint64_t kRAXOffset = 2216;

llvm::Value *buildStateLoad(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                            uint64_t offset, const llvm::Twine &name) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  return Builder.CreateLoad(Builder.getInt64Ty(), gep, name);
}

llvm::Value *buildStateLoadVec(llvm::IRBuilder<> &Builder,
                                llvm::Value *state_ptr, uint64_t offset,
                                const llvm::Twine &name) {
  auto *vec_ty = llvm::FixedVectorType::get(Builder.getInt64Ty(), 2);
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  return Builder.CreateLoad(vec_ty, gep, name);
}

void buildStateStore(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                     uint64_t offset, llvm::Value *val) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  Builder.CreateStore(val, gep);
}

/// Check if a function has the remill lifted signature: (ptr, i64, ptr) -> ptr.
bool hasLiftedSignature(const llvm::Function &F) {
  if (F.arg_size() != 3) return false;
  auto *FTy = F.getFunctionType();
  if (!FTy->getReturnType()->isPointerTy()) return false;
  if (!FTy->getParamType(0)->isPointerTy()) return false;
  if (!FTy->getParamType(1)->isIntegerTy(64)) return false;
  if (!FTy->getParamType(2)->isPointerTy()) return false;
  return true;
}

/// Check if a lifted function is a "leaf" — it doesn't call other lifted
/// functions or dispatch_call/dispatch_jump.  Leaf functions can be safely
/// inlined directly (sharing the caller's State pointer) instead of going
/// through a _native wrapper, which preserves flag/State field semantics.
bool isLeafLifted(const llvm::Function &F, const LiftedFunctionMap &lifted) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call) continue;
      auto *callee = call->getCalledFunction();
      if (!callee) continue;

      // Calls to other lifted functions.
      if (isLiftedFunction(*callee))
        return false;
      // Calls to lifted forward declarations.
      if (callee->isDeclaration() && hasLiftedSignature(*callee) &&
          callee->getName().starts_with("sub_"))
        return false;
      // Dispatch calls/jumps.
      if (callee->getName() == "__omill_dispatch_call" ||
          callee->getName() == "__omill_dispatch_jump")
        return false;
    }
  }
  return true;
}

struct RewriteCandidate {
  llvm::CallInst *call;
  llvm::Function *lifted_definition;  // nullptr for dynamic dispatch
  llvm::Value *state_ptr;
};

/// Resolve a callee to the defined lifted function.
llvm::Function *resolveToDefinition(llvm::Function *callee,
                                     const LiftedFunctionMap &lifted) {
  if (isLiftedFunction(*callee))
    return callee;

  if (callee->isDeclaration() && hasLiftedSignature(*callee) &&
      callee->getName().starts_with("sub_")) {
    uint64_t va = extractEntryVA(callee->getName());
    if (va != 0)
      return lifted.lookup(va);
  }

  return nullptr;
}

/// Rewrite a direct call to a forward declaration so it targets the actual
/// definition instead.  This ensures AlwaysInlinerPass can inline it.
void fixupForwardDeclarationCall(llvm::CallInst *call,
                                  llvm::Function *definition) {
  auto *callee = call->getCalledFunction();
  if (callee == definition) return;  // Already targeting the definition.

  // The declaration and definition have the same type (lifted signature).
  call->setCalledFunction(definition->getFunctionType(), definition);
}

void collectCandidates(llvm::Function &F, const LiftedFunctionMap &lifted,
                       llvm::SmallVectorImpl<RewriteCandidate> &candidates) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call) continue;

      auto *callee = call->getCalledFunction();
      if (!callee) continue;

      // Pattern A: direct call to lifted function (defined or declaration).
      if (call->arg_size() >= 1 && callee->getName().starts_with("sub_")) {
        auto *def = resolveToDefinition(callee, lifted);
        if (def) {
          // Leaf functions: don't rewrite — let AlwaysInlinerPass inline them
          // directly, preserving flag/State field semantics.  Just fix the
          // call target if it's a forward declaration.
          if (isLeafLifted(*def, lifted)) {
            fixupForwardDeclarationCall(call, def);
            continue;
          }
          candidates.push_back({call, def, call->getArgOperand(0)});
          continue;
        }
      }

      // Pattern B: __omill_dispatch_call or __omill_dispatch_jump.
      bool is_dispatch =
          callee->getName() == "__omill_dispatch_call" ||
          callee->getName() == "__omill_dispatch_jump";
      if (!is_dispatch || call->arg_size() < 3)
        continue;

      auto *target_arg = call->getArgOperand(1);

      // B1: ptrtoint(@func) — resolved target.
      if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target_arg)) {
        if (auto *target_fn =
                llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand())) {
          auto *def = resolveToDefinition(target_fn, lifted);
          if (def) {
            candidates.push_back({call, def, call->getArgOperand(0)});
            continue;
          }
        }
      }

      // B2: ConstantInt(pc) — look up by PC value.
      if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(target_arg)) {
        auto *def = lifted.lookup(ci->getZExtValue());
        if (def) {
          candidates.push_back({call, def, call->getArgOperand(0)});
          continue;
        }
      }

      // B3: Dynamic target — still rewrite to prevent State escape.
      candidates.push_back({call, nullptr, call->getArgOperand(0)});
    }
  }
}

/// Collect the sorted union of all XMM live-in offsets across all lifted
/// functions that could be dispatch targets.
void collectAllXMMOffsets(llvm::Module &M, const CallingConventionInfo &cc_info,
                          llvm::SmallVectorImpl<unsigned> &xmm_offsets) {
  llvm::DenseSet<unsigned> seen;
  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;
    auto *abi = cc_info.getABI(&F);
    if (!abi) continue;
    for (auto off : abi->xmm_live_ins) {
      if (seen.insert(off).second) {
        xmm_offsets.push_back(off);
      }
    }
  }
  llvm::sort(xmm_offsets);
}

/// Create or get the native dispatch function that maps original PCs to
/// _native wrapper calls.
/// Signature: i64(i64 pc, i64 rcx, i64 rdx, i64 r8, i64 r9, <2 x i64>...).
/// XMM values are passed as extra params (no State pointer — avoids escaping
/// the State alloca which would prevent dead store elimination).
llvm::Function *getOrCreateNativeDispatch(
    llvm::Module &M, const LiftedFunctionMap &lifted,
    const CallingConventionInfo &cc_info,
    const llvm::SmallVectorImpl<unsigned> &all_xmm_offsets) {
  auto *existing = M.getFunction("__omill_native_dispatch");
  if (existing) return existing;

  auto &Ctx = M.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *vec_ty = llvm::FixedVectorType::get(i64_ty, 2);

  // Build param types: pc, rcx, rdx, r8, r9, then XMM params.
  llvm::SmallVector<llvm::Type *, 24> param_types;
  param_types.push_back(i64_ty);  // pc
  param_types.push_back(i64_ty);  // rcx
  param_types.push_back(i64_ty);  // rdx
  param_types.push_back(i64_ty);  // r8
  param_types.push_back(i64_ty);  // r9
  for (unsigned i = 0; i < all_xmm_offsets.size(); ++i) {
    param_types.push_back(vec_ty);
  }

  auto *fn_ty = llvm::FunctionType::get(i64_ty, param_types, false);
  auto *fn = llvm::Function::Create(
      fn_ty, llvm::Function::InternalLinkage, "__omill_native_dispatch", M);
  fn->addFnAttr(llvm::Attribute::NoUnwind);

  // Build offset-to-param-index map for XMM params.
  llvm::DenseMap<unsigned, unsigned> xmm_param_idx;
  for (unsigned i = 0; i < all_xmm_offsets.size(); ++i) {
    xmm_param_idx[all_xmm_offsets[i]] = 5 + i;  // after pc,rcx,rdx,r8,r9
  }

  auto *entry_bb = llvm::BasicBlock::Create(Ctx, "entry", fn);
  auto *default_bb = llvm::BasicBlock::Create(Ctx, "unknown", fn);

  {
    llvm::IRBuilder<> Builder(default_bb);
    Builder.CreateRet(Builder.getInt64(0));
  }

  llvm::IRBuilder<> Builder(entry_bb);
  auto *pc_arg = fn->getArg(0);
  auto *sw = Builder.CreateSwitch(pc_arg, default_bb);

  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;

    uint64_t va = extractEntryVA(F.getName());
    if (va == 0) continue;

    auto *abi = cc_info.getABI(&F);
    if (!abi) continue;

    auto *case_bb = llvm::BasicBlock::Create(Ctx,
        "call_" + llvm::Twine::utohexstr(va), fn);
    sw->addCase(Builder.getInt64(va), case_bb);

    llvm::IRBuilder<> CaseB(case_bb);

    std::string native_name = F.getName().str() + "_native";
    auto *native_fn = M.getFunction(native_name);

    // Pass GPR args from dispatch params.
    llvm::SmallVector<llvm::Value *, 8> args;
    for (unsigned i = 0; i < abi->numParams(); ++i) {
      args.push_back(fn->getArg(1 + i));  // skip pc, take rcx/rdx/r8/r9
    }

    // Pass XMM values from dispatch params (not from State).
    for (auto xmm_off : abi->xmm_live_ins) {
      auto it = xmm_param_idx.find(xmm_off);
      assert(it != xmm_param_idx.end());
      args.push_back(fn->getArg(it->second));
    }

    auto *result = CaseB.CreateCall(native_fn, args);
    if (abi->ret.has_value()) {
      CaseB.CreateRet(result);
    } else {
      CaseB.CreateRet(CaseB.getInt64(0));
    }
  }

  return fn;
}

}  // namespace

llvm::PreservedAnalyses RewriteLiftedCallsToNativePass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &cc_info = MAM.getResult<CallingConventionAnalysis>(M);
  auto &lifted = MAM.getResult<LiftedFunctionAnalysis>(M);

  bool changed = false;
  llvm::Function *dispatch_fn = nullptr;
  llvm::SmallVector<unsigned, 16> all_xmm_offsets;

  for (auto &F : M) {
    if (F.isDeclaration()) continue;

    llvm::SmallVector<RewriteCandidate, 8> candidates;
    collectCandidates(F, lifted, candidates);
    if (candidates.empty()) continue;

    for (auto &cand : candidates) {
      if (cand.lifted_definition) {
        // Static target: call the _native wrapper directly.
        std::string native_name =
            cand.lifted_definition->getName().str() + "_native";
        auto *native_fn = M.getFunction(native_name);
        if (!native_fn) continue;

        if (native_fn == &F) continue;

        auto *abi = cc_info.getABI(cand.lifted_definition);
        if (!abi) continue;

        llvm::IRBuilder<> Builder(cand.call);

        llvm::SmallVector<llvm::Value *, 8> args;
        for (auto &param : abi->params) {
          args.push_back(buildStateLoad(
              Builder, cand.state_ptr, param.state_offset,
              llvm::StringRef(param.reg_name).lower()));
        }

        // Pass XMM live-in values from State as extra <2 x i64> args.
        for (auto xmm_off : abi->xmm_live_ins) {
          args.push_back(buildStateLoadVec(
              Builder, cand.state_ptr, xmm_off,
              "xmm_" + llvm::Twine(xmm_off)));
        }

        auto *result = Builder.CreateCall(native_fn, args,
                                          abi->ret.has_value()
                                              ? native_fn->getName() + ".result"
                                              : "");

        if (abi->ret.has_value()) {
          buildStateStore(Builder, cand.state_ptr, abi->ret->state_offset,
                          result);
        }
      } else {
        // Dynamic target: dispatch through the native dispatch function.
        // Collect all XMM offsets on first use.
        if (!dispatch_fn) {
          collectAllXMMOffsets(M, cc_info, all_xmm_offsets);
          dispatch_fn = getOrCreateNativeDispatch(M, lifted, cc_info,
                                                   all_xmm_offsets);
        }

        llvm::IRBuilder<> Builder(cand.call);

        auto *target_pc = cand.call->getArgOperand(1);
        auto *rcx =
            buildStateLoad(Builder, cand.state_ptr, kRCXOffset, "rcx");
        auto *rdx =
            buildStateLoad(Builder, cand.state_ptr, kRDXOffset, "rdx");
        auto *r8 =
            buildStateLoad(Builder, cand.state_ptr, kR8Offset, "r8");
        auto *r9 =
            buildStateLoad(Builder, cand.state_ptr, kR9Offset, "r9");

        // Load XMM values from State for all possible dispatch targets.
        llvm::SmallVector<llvm::Value *, 24> dispatch_args;
        dispatch_args.push_back(target_pc);
        dispatch_args.push_back(rcx);
        dispatch_args.push_back(rdx);
        dispatch_args.push_back(r8);
        dispatch_args.push_back(r9);
        for (auto xmm_off : all_xmm_offsets) {
          dispatch_args.push_back(buildStateLoadVec(
              Builder, cand.state_ptr, xmm_off,
              "xmm_" + llvm::Twine(xmm_off)));
        }

        auto *result = Builder.CreateCall(
            dispatch_fn, dispatch_args, "dispatch.result");

        buildStateStore(Builder, cand.state_ptr, kRAXOffset, result);
      }

      if (!cand.call->getType()->isVoidTy()) {
        cand.call->replaceAllUsesWith(
            llvm::PoisonValue::get(cand.call->getType()));
      }
      cand.call->eraseFromParent();
      changed = true;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
