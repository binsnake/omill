#pragma once

#include <cstdint>
#include <llvm/IR/PassManager.h>

namespace omill {

namespace OptimizePhases {
enum : uint32_t {
  DeadStores = 1 << 1,
  RedundantBytes = 1 << 2,
  Promote = 1 << 3,
  Roundtrip = 1 << 4,
  // Presets
  Early = DeadStores | Promote,
  All = 0xFFFFFFFF,
};
}  // namespace OptimizePhases

/// Consolidated pass for State struct optimization.
///
/// Phases (executed in order when enabled via bitmask):
///  1. DeadStores — eliminate dead stores to all State fields (intra-block)
///  2. RedundantBytes — eliminate narrow constant stores subsumed by wider
///  3. Promote — promote State fields to SSA allocas
///  4. Roundtrip — eliminate redundant load→store roundtrips
class OptimizeStatePass : public llvm::PassInfoMixin<OptimizeStatePass> {
 public:
  explicit OptimizeStatePass(uint32_t phases = OptimizePhases::All)
      : phases_(phases) {}

  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM);

  static llvm::StringRef name() { return "OptimizeStatePass"; }

 private:
  uint32_t phases_;
};

}  // namespace omill
