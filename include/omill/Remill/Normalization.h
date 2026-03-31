#pragma once

#include <functional>
#include <string>
#include <vector>

#include <llvm/IR/PassManager.h>

namespace llvm {
class Function;
class Module;
}

namespace omill {

enum class RemillNormalizationEpoch {
  kInitialLift,
  kIncrementalRound,
  kPreMaterialization,
  kPreFinalize,
  kFinalVerification,
};

struct RemillNormalizationRequest {
  RemillNormalizationEpoch epoch = RemillNormalizationEpoch::kInitialLift;
  bool no_abi_mode = false;
  bool aggressive_folding = false;
  std::function<bool(llvm::Function &)> scope_predicate;
  bool include_semantic_helpers = false;
};

struct RemillNormalizationSummary {
  unsigned unresolved_dispatch_intrinsics = 0;
  unsigned live_memory_intrinsics = 0;
  unsigned live_runtime_intrinsics = 0;
  unsigned legacy_omill_dispatch_intrinsics = 0;
  unsigned native_wrapper_functions = 0;
  bool verifier_clean = true;
  std::vector<std::string> diagnostics;
};

class RemillNormalizationOrchestrator {
 public:
  RemillNormalizationSummary summarize(const llvm::Module &M) const;
  void appendToPipeline(llvm::ModulePassManager &MPM,
                        const RemillNormalizationRequest &request) const;
};

const char *toString(RemillNormalizationEpoch epoch);

}  // namespace omill
