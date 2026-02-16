#include "omill/Passes/RewriteLiftedCallsToNative.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

llvm::Value *buildStateLoad(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                            uint64_t offset, const llvm::Twine &name) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  return Builder.CreateLoad(Builder.getInt64Ty(), gep, name);
}

void buildStateStore(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                     uint64_t offset, llvm::Value *val) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  Builder.CreateStore(val, gep);
}

/// Try to resolve a call target to a lifted function.
/// Returns the lifted Function* if the callee is a lifted function, or if
/// it's a dispatch_call with ptrtoint(@sub_X) as target.
struct RewriteCandidate {
  llvm::CallInst *call;
  llvm::Function *lifted_target;
  llvm::Value *state_ptr;
  bool is_dispatch;  // true = __omill_dispatch_call pattern
};

/// Collect all calls that target lifted functions (directly or via dispatch).
void collectCandidates(llvm::Function &F,
                       llvm::SmallVectorImpl<RewriteCandidate> &candidates) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call) continue;

      auto *callee = call->getCalledFunction();
      if (!callee) continue;

      // Pattern A: direct call to lifted function sub_Y(State*, pc, Memory*)
      if (isLiftedFunction(*callee) && call->arg_size() >= 1) {
        candidates.push_back(
            {call, callee, call->getArgOperand(0), /*is_dispatch=*/false});
        continue;
      }

      // Pattern B: __omill_dispatch_call(State*, ptrtoint(@sub_Y), Memory*)
      if (callee->getName() == "__omill_dispatch_call" &&
          call->arg_size() >= 3) {
        auto *ptoi =
            llvm::dyn_cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
        if (!ptoi) continue;
        auto *target_fn =
            llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
        if (!target_fn) continue;
        // Only rewrite if target is a lifted function (not dllimport).
        if (!isLiftedFunction(*target_fn)) continue;

        candidates.push_back({call, target_fn, call->getArgOperand(0),
                              /*is_dispatch=*/true});
      }
    }
  }
}

}  // namespace

llvm::PreservedAnalyses RewriteLiftedCallsToNativePass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &cc_info = MAM.getResult<CallingConventionAnalysis>(M);

  bool changed = false;

  // Process all functions (including _native wrappers — after inlining,
  // calls to other lifted functions end up inside them).
  for (auto &F : M) {
    if (F.isDeclaration()) continue;

    llvm::SmallVector<RewriteCandidate, 8> candidates;
    collectCandidates(F, candidates);
    if (candidates.empty()) continue;

    for (auto &cand : candidates) {
      // Look up the native wrapper.
      std::string native_name = cand.lifted_target->getName().str() + "_native";
      auto *native_fn = M.getFunction(native_name);
      if (!native_fn) continue;

      // Don't rewrite the call inside a wrapper to its own lifted function —
      // that's the call that AlwaysInlinerPass will inline.
      if (native_fn == &F) continue;

      // Get ABI for the target.
      auto *abi = cc_info.getABI(cand.lifted_target);
      if (!abi) continue;

      llvm::IRBuilder<> Builder(cand.call);

      // Load parameter registers from State.
      llvm::SmallVector<llvm::Value *, 4> args;
      for (auto &param : abi->params) {
        args.push_back(buildStateLoad(Builder, cand.state_ptr,
                                      param.state_offset,
                                      llvm::StringRef(param.reg_name).lower()));
      }

      // Call the native wrapper.
      auto *result = Builder.CreateCall(native_fn, args,
                                        abi->ret.has_value()
                                            ? native_fn->getName() + ".result"
                                            : "");

      // Store return value back to State.
      if (abi->ret.has_value()) {
        buildStateStore(Builder, cand.state_ptr, abi->ret->state_offset,
                        result);
      }

      // Replace uses of the old call (Memory* token) with poison.
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
