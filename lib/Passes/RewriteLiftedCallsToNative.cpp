#include "omill/Passes/RewriteLiftedCallsToNative.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"
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

void buildStateStoreVec(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                        uint64_t offset, llvm::Value *val) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  Builder.CreateStore(val, gep);
}

llvm::Value *normalizeJumpTargetPC(llvm::IRBuilder<> &Builder,
                                   llvm::Value *target_pc,
                                   const BinaryMemoryMap *map) {
  if (!map) {
    return target_pc;
  }

  uint64_t image_base = map->imageBase();
  uint64_t image_size = map->imageSize();
  if (image_base == 0 || image_size == 0) {
    return target_pc;
  }

  auto *i64_ty = Builder.getInt64Ty();
  auto *i32_ty = Builder.getInt32Ty();
  auto *base_c = llvm::ConstantInt::get(i64_ty, image_base);
  auto *size_c = llvm::ConstantInt::get(i64_ty, image_size);

  // Keep already-canonical in-image targets untouched.
  auto *delta = Builder.CreateSub(target_pc, base_c, "pc.delta");
  auto *in_image = Builder.CreateICmpULT(delta, size_c, "pc.in_image");

  // Canonicalize RVA-like and +4GB-skewed forms:
  //   0x1a6a       -> 0x140001a6a
  //   0x100001a6a  -> 0x140001a6a
  //   0x240001a6a  -> 0x140001a6a
  auto *low32 = Builder.CreateZExt(Builder.CreateTrunc(target_pc, i32_ty),
                                    i64_ty, "pc.low32");
  auto *low32_in_image =
      Builder.CreateICmpULT(low32, size_c, "pc.low32_in_image");
  auto *low32_as_va = Builder.CreateAdd(base_c, low32, "pc.low32_as_va");
  auto *normalized = Builder.CreateSelect(low32_in_image, low32_as_va, target_pc,
                                          "pc.norm");

  // Also handle targets already rebased to image_base but skewed by +4GB
  // in the RVA component, e.g. 0x240001a6a -> 0x140001a6a.
  auto *as_rva = Builder.CreateSub(target_pc, base_c, "pc.as_rva");
  auto *as_rva_low32 = Builder.CreateZExt(
      Builder.CreateTrunc(as_rva, i32_ty), i64_ty, "pc.as_rva_low32");
  auto *as_rva_low32_in_image =
      Builder.CreateICmpULT(as_rva_low32, size_c, "pc.as_rva_low32_in_image");
  auto *as_rva_low32_as_va =
      Builder.CreateAdd(base_c, as_rva_low32, "pc.as_rva_low32_as_va");
  normalized = Builder.CreateSelect(as_rva_low32_in_image, as_rva_low32_as_va,
                                    normalized, "pc.norm.rebased");

  return Builder.CreateSelect(in_image, target_pc, normalized,
                              "pc.canonical");
}

// hasLiftedSignature is now in omill/Utils/LiftedNames.h

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
  bool is_dispatch_jump;
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
                       const llvm::DenseSet<const llvm::Function *> &non_leaf_set,
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
          if (!non_leaf_set.count(def)) {
            fixupForwardDeclarationCall(call, def);
            continue;
          }
          candidates.push_back({call, def, call->getArgOperand(0), false});
          continue;
        }
      }

      // Pattern B: __omill_dispatch_call or __omill_dispatch_jump.
      bool is_dispatch =
          callee->getName() == "__omill_dispatch_call" ||
          callee->getName() == "__omill_dispatch_jump";
      if (!is_dispatch || call->arg_size() < 3)
        continue;
      bool is_dispatch_jump = callee->getName() == "__omill_dispatch_jump";

      auto *target_arg = call->getArgOperand(1);

      // B1: ptrtoint(@func) — resolved target.
      if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target_arg)) {
        if (auto *target_fn =
                llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand())) {
          auto *def = resolveToDefinition(target_fn, lifted);
          if (def) {
            candidates.push_back(
                {call, def, call->getArgOperand(0), is_dispatch_jump});
            continue;
          }
        }
      }
      // B2: ConstantInt(pc) -> look up by PC value.
      if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(target_arg)) {
        const auto &pc_ap = ci->getValue();
        // Some obfuscated paths synthesize oversized integer widths.
        // Only treat values that fit in 64-bit VA space as direct targets.
        if (pc_ap.getActiveBits() <= 64) {
          auto *def = lifted.lookup(pc_ap.getZExtValue());
          if (def) {
            candidates.push_back(
                {call, def, call->getArgOperand(0), is_dispatch_jump});
            continue;
          }
        }
      }

      // B3: Dynamic target — still rewrite to prevent State escape.
      // Keep unresolved jump dispatches as calls to __omill_dispatch_jump.
      // Rewriting them to inttoptr(target_pc) can call raw binary VAs.
      if (is_dispatch_jump) {
        if (F.getName().ends_with("_native")) {
          candidates.push_back({call, nullptr, call->getArgOperand(0), true});
        }
        continue;
      }

      candidates.push_back({call, nullptr, call->getArgOperand(0), false});
    }
  }
}

}  // namespace

llvm::PreservedAnalyses RewriteLiftedCallsToNativePass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &cc_info = MAM.getResult<CallingConventionAnalysis>(M);
  auto &lifted = MAM.getResult<LiftedFunctionAnalysis>(M);
  auto &mem_map = MAM.getResult<BinaryMemoryAnalysis>(M);

  // Pre-compute leaf status for all lifted functions before any mutations.
  // This prevents isLeafLifted from returning stale results after dispatch
  // calls in earlier functions are erased during processing.
  llvm::DenseSet<const llvm::Function *> non_leaf_set;
  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;
    if (!isLeafLifted(F, lifted))
      non_leaf_set.insert(&F);
  }

  bool changed = false;

  for (auto &F : M) {
    if (F.isDeclaration()) continue;

    llvm::SmallVector<RewriteCandidate, 8> candidates;
    collectCandidates(F, lifted, non_leaf_set, candidates);
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

        llvm::SmallVector<llvm::Value *, 12> args;

        // GPR params from State.
        for (auto &param : abi->params) {
          args.push_back(buildStateLoad(
              Builder, cand.state_ptr, param.state_offset,
              llvm::StringRef(param.reg_name).lower()));
        }

        // Stack-passed params: load from caller's RSP-relative stack area.
        for (auto &sp : abi->stack_params) {
          // Load RSP, add stack_offset, load the value from that address.
          auto *rsp_val = buildStateLoad(Builder, cand.state_ptr,
                                         48, "rsp_for_stack");
          auto *addr = Builder.CreateAdd(
              rsp_val, Builder.getInt64(sp.stack_offset),
              "stack_arg_addr");
          auto *ptr = Builder.CreateIntToPtr(
              addr, llvm::PointerType::get(Builder.getContext(), 0));
          auto *val = Builder.CreateLoad(Builder.getInt64Ty(), ptr,
                                         "stack_arg");
          args.push_back(val);
        }

        // XMM live-in values from State as extra <2 x i64> args.
        for (auto xmm_off : abi->xmm_live_ins) {
          args.push_back(buildStateLoadVec(
              Builder, cand.state_ptr, xmm_off,
              "xmm_" + llvm::Twine(xmm_off)));
        }

        // Extra GPR live-in values from State as extra i64 args.
        for (auto gpr_off : abi->extra_gpr_live_ins) {
          args.push_back(buildStateLoad(
              Builder, cand.state_ptr, gpr_off,
              "extra_gpr_" + llvm::Twine(gpr_off)));
        }

        auto *result = Builder.CreateCall(native_fn, args,
                                          abi->ret.has_value()
                                              ? native_fn->getName() + ".result"
                                              : "");

        if (abi->ret.has_value()) {
          if (abi->ret->is_vector) {
            buildStateStoreVec(Builder, cand.state_ptr,
                               abi->ret->state_offset, result);
          } else {
            buildStateStore(Builder, cand.state_ptr,
                            abi->ret->state_offset, result);
          }
        }
      } else {
        // Dynamic dispatch_call target: emit an indirect call through target PC.
        // Dynamic dispatch_jump in _native wrappers: materialize RAX only.
        llvm::IRBuilder<> Builder(cand.call);
        auto *i64_ty = Builder.getInt64Ty();
        auto *target_pc = cand.call->getArgOperand(1);

        if (cand.is_dispatch_jump) {
          if (!target_pc->getType()->isIntegerTy(64)) {
            if (target_pc->getType()->isPointerTy()) {
              target_pc = Builder.CreatePtrToInt(target_pc, i64_ty, "jump.pc");
            } else if (target_pc->getType()->isIntegerTy()) {
              target_pc = Builder.CreateZExtOrTrunc(target_pc, i64_ty, "jump.pc");
            } else {
              target_pc = llvm::PoisonValue::get(i64_ty);
            }
          }
          target_pc = normalizeJumpTargetPC(Builder, target_pc, &mem_map);
          buildStateStore(Builder, cand.state_ptr, kRAXOffset, target_pc);
        } else {
          auto *ptr_ty = llvm::PointerType::get(Builder.getContext(), 0);
          auto *fn_ptr = Builder.CreateIntToPtr(target_pc, ptr_ty, "fn.ptr");

          auto *rcx =
              buildStateLoad(Builder, cand.state_ptr, kRCXOffset, "rcx");
          auto *rdx =
              buildStateLoad(Builder, cand.state_ptr, kRDXOffset, "rdx");
          auto *r8 =
              buildStateLoad(Builder, cand.state_ptr, kR8Offset, "r8");
          auto *r9 =
              buildStateLoad(Builder, cand.state_ptr, kR9Offset, "r9");

          auto *fn_ty = llvm::FunctionType::get(
              i64_ty, {i64_ty, i64_ty, i64_ty, i64_ty}, false);

          auto *result = Builder.CreateCall(fn_ty, fn_ptr,
                                            {rcx, rdx, r8, r9},
                                            "indirect.result");
          // This call is not structurally in tail position in many lifted
          // functions, so using musttail here can produce invalid IR.
          llvm::cast<llvm::CallInst>(result)->setTailCallKind(
              llvm::CallInst::TCK_Tail);

          buildStateStore(Builder, cand.state_ptr, kRAXOffset, result);
        }
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
