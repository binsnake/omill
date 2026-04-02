#include "omill/Remill/Normalization.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>

#include "omill/Omill.h"
#include "omill/Passes/CombinedFixedPointDevirt.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

bool shouldNormalizeFunction(llvm::Function &F,
                             const RemillNormalizationRequest &request) {
  if (F.isDeclaration())
    return false;
  if (request.scope_predicate && request.scope_predicate(F))
    return true;
  if (hasLiftedSignature(F))
    return true;
  if (!request.include_semantic_helpers)
    return false;

  const auto name = F.getName();
  if (name.starts_with("__remill_") || name.starts_with("__omill_") ||
      name.starts_with("llvm."))
    return false;
  return true;
}

unsigned countCallsMatching(const llvm::Module &M,
                            llvm::function_ref<bool(llvm::StringRef)> pred) {
  unsigned count = 0;
  for (const auto &F : M) {
    for (const auto &BB : F) {
      for (const auto &I : BB) {
        const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        const auto *callee = CB ? CB->getCalledFunction() : nullptr;
        if (callee && pred(callee->getName()))
          ++count;
      }
    }
  }
  return count;
}

unsigned countLiveDeclarations(const llvm::Module &M,
                               llvm::function_ref<bool(llvm::StringRef)> pred) {
  unsigned count = 0;
  for (const auto &F : M) {
    if (pred(F.getName()) && !F.use_empty())
      ++count;
  }
  return count;
}

// Intentional compatibility boundary: keep canonicalization of legacy
// __omill_dispatch_* spellings fenced here so driver/runtime cleanup does not
// need to carry legacy dispatch-name conditionals.
struct CanonicalizeLegacyDispatchPass
    : llvm::PassInfoMixin<CanonicalizeLegacyDispatchPass> {
  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &) {
    bool changed = false;
    auto canonicalizeOne = [&](llvm::StringRef legacy_name,
                               llvm::StringRef canonical_name) {
      auto *legacy = M.getFunction(legacy_name);
      if (!legacy)
        return;

      auto canonical_callee =
          M.getOrInsertFunction(canonical_name, legacy->getFunctionType());
      auto *canonical =
          llvm::dyn_cast<llvm::Function>(canonical_callee.getCallee());
      if (!canonical)
        return;

      llvm::SmallVector<llvm::CallBase *, 16> calls;
      for (auto *U : legacy->users()) {
        if (auto *CB = llvm::dyn_cast<llvm::CallBase>(U))
          calls.push_back(CB);
      }

      for (auto *CB : calls) {
        llvm::IRBuilder<> B(CB);
        llvm::SmallVector<llvm::Value *, 8> args;
        args.reserve(CB->arg_size());
        for (auto &arg : CB->args())
          args.push_back(arg.get());
        auto *replacement = B.CreateCall(canonical->getFunctionType(),
                                         canonical, args);
        replacement->setCallingConv(CB->getCallingConv());
        replacement->setAttributes(CB->getAttributes());
        if (!CB->use_empty())
          CB->replaceAllUsesWith(replacement);
        CB->eraseFromParent();
        changed = true;
      }

      if (legacy->use_empty() && legacy->isDeclaration()) {
        legacy->eraseFromParent();
        changed = true;
      }
    };

    canonicalizeOne("__omill_dispatch_call", "__remill_function_call");
    canonicalizeOne("__omill_dispatch_jump", "__remill_jump");
    return changed ? llvm::PreservedAnalyses::none()
                   : llvm::PreservedAnalyses::all();
  }
  static bool isRequired() { return true; }
};

}  // namespace

RemillNormalizationSummary RemillNormalizationOrchestrator::summarize(
    const llvm::Module &M) const {
  RemillNormalizationSummary summary;
  summary.unresolved_dispatch_intrinsics = countCallsMatching(
      M, [](llvm::StringRef name) { return isDispatchIntrinsicName(name); });
  summary.live_memory_intrinsics = countLiveDeclarations(
      M, [](llvm::StringRef name) {
        return name.starts_with("__remill_read_memory_") ||
               name.starts_with("__remill_write_memory_");
      });
  summary.live_runtime_intrinsics = countLiveDeclarations(
      M, [](llvm::StringRef name) {
        return name.starts_with("__remill_") &&
               !isDispatchIntrinsicName(name) &&
               name != "__remill_basic_block";
      });
  summary.legacy_omill_dispatch_intrinsics = countCallsMatching(
      M, [](llvm::StringRef name) { return isLegacyOmillDispatchName(name); });

  llvm::raw_null_ostream nulls;
  summary.verifier_clean = !llvm::verifyModule(M, &nulls);
  if (!summary.verifier_clean)
    summary.diagnostics.emplace_back("module_verifier_failed");
  if (summary.legacy_omill_dispatch_intrinsics != 0) {
    summary.diagnostics.emplace_back("legacy_omill_dispatch_present");
  }
  return summary;
}

void RemillNormalizationOrchestrator::appendToPipeline(
    llvm::ModulePassManager &MPM,
    const RemillNormalizationRequest &request) const {
  llvm::FunctionPassManager FPM;

  auto categories = LowerCategories::Flags | LowerCategories::Barriers |
                    LowerCategories::Memory | LowerCategories::Atomics |
                    LowerCategories::HyperCalls | LowerCategories::Undefined;

  if (request.epoch == RemillNormalizationEpoch::kPreMaterialization ||
      request.epoch == RemillNormalizationEpoch::kPreFinalize ||
      request.epoch == RemillNormalizationEpoch::kFinalVerification) {
    categories = categories | LowerCategories::ErrorMissing |
                 LowerCategories::Return | LowerCategories::Call |
                 LowerCategories::Jump | LowerCategories::ResolvedDispatch;
  }

  FPM.addPass(LowerRemillIntrinsicsPass(categories));
  if (request.aggressive_folding) {
    FPM.addPass(CombinedFixedPointDevirtPass());
    FPM.addPass(llvm::GVNPass());
    FPM.addPass(llvm::ADCEPass());
    FPM.addPass(llvm::SimplifyCFGPass());
    FPM.addPass(CombinedFixedPointDevirtPass());
  } else {
    buildCleanupPipeline(FPM, CleanupProfile::kLightScalar);
  }

  struct ScopedNormalizationPass
      : llvm::PassInfoMixin<ScopedNormalizationPass> {
    llvm::FunctionPassManager FPM;
    RemillNormalizationRequest request;

    ScopedNormalizationPass(llvm::FunctionPassManager fnpm,
                            RemillNormalizationRequest req)
        : FPM(std::move(fnpm)), request(std::move(req)) {}

    llvm::PreservedAnalyses run(llvm::Module &M,
                                llvm::ModuleAnalysisManager &MAM) {
      auto &FAM =
          MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
              .getManager();
      bool changed = false;
      for (auto &F : M) {
        if (!shouldNormalizeFunction(F, request))
          continue;
        auto PA = FPM.run(F, FAM);
        if (!PA.areAllPreserved()) {
          changed = true;
          FAM.invalidate(F, PA);
        }
      }
      return changed ? llvm::PreservedAnalyses::none()
                     : llvm::PreservedAnalyses::all();
    }
    static bool isRequired() { return true; }
  };

  MPM.addPass(ScopedNormalizationPass(std::move(FPM), request));
  if (request.epoch == RemillNormalizationEpoch::kFinalVerification)
    MPM.addPass(CanonicalizeLegacyDispatchPass{});
}

const char *toString(RemillNormalizationEpoch epoch) {
  switch (epoch) {
    case RemillNormalizationEpoch::kInitialLift:
      return "initial_lift";
    case RemillNormalizationEpoch::kIncrementalRound:
      return "incremental_round";
    case RemillNormalizationEpoch::kPreMaterialization:
      return "pre_materialization";
    case RemillNormalizationEpoch::kPreFinalize:
      return "pre_finalize";
    case RemillNormalizationEpoch::kFinalVerification:
      return "final_verification";
  }
  return "initial_lift";
}

}  // namespace omill
