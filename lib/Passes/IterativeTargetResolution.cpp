#include "omill/Passes/IterativeTargetResolution.h"

#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Utils/FixIrreducible.h>
#include <llvm/Transforms/Utils/LCSSA.h>
#include <llvm/Transforms/Utils/LoopSimplify.h>

#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/EliminateDeadPaths.h"
#include "omill/Passes/LowerResolvedDispatchCalls.h"
#include "omill/Passes/RecoverJumpTables.h"
#include "omill/Passes/ResolveDispatchTargets.h"
#include "omill/Passes/SymbolicJumpTableSolver.h"
#if OMILL_ENABLE_Z3
#include "omill/Passes/Z3DispatchSolver.h"
#endif

namespace omill {

namespace {

/// Count unresolved __omill_dispatch_call and __omill_dispatch_jump calls.
unsigned countUnresolvedDispatches(llvm::Module &M) {
  unsigned count = 0;
  for (auto &F : M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name == "__omill_dispatch_call" || name == "__omill_dispatch_jump")
          ++count;
      }
    }
  }
  return count;
}

}  // namespace

llvm::PreservedAnalyses IterativeTargetResolutionPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  unsigned iteration = 0;
  unsigned prev_count = countUnresolvedDispatches(M);

  if (prev_count == 0)
    return llvm::PreservedAnalyses::all();

  bool ever_changed = false;

  do {
    // Step 1: CFG canonicalization + LLVM optimizations.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::FixIrreduciblePass());
      FPM.addPass(llvm::LoopSimplifyPass());
      FPM.addPass(llvm::LCSSAPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      FPM.addPass(ConstantMemoryFoldingPass());
      FPM.addPass(EliminateDeadPathsPass());
      FPM.addPass(llvm::InstCombinePass());
      auto adaptor = llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
      adaptor.run(M, MAM);
    }

    // Step 2: Resolve dispatch targets and lower resolved calls.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(ResolveDispatchTargetsPass());
      FPM.addPass(RecoverJumpTablesPass());
      FPM.addPass(SymbolicJumpTableSolverPass());
#if OMILL_ENABLE_Z3
      FPM.addPass(Z3DispatchSolverPass());
#endif
      FPM.addPass(LowerResolvedDispatchCallsPass());
      auto adaptor = llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
      adaptor.run(M, MAM);
    }

    unsigned curr_count = countUnresolvedDispatches(M);
    if (curr_count < prev_count)
      ever_changed = true;

    if (curr_count >= prev_count)
      break;

    prev_count = curr_count;
    ++iteration;
  } while (iteration < max_iterations_);

  return ever_changed ? llvm::PreservedAnalyses::none()
                      : llvm::PreservedAnalyses::all();
}

}  // namespace omill
