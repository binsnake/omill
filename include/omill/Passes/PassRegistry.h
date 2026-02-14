#pragma once

#include <llvm/IR/PassManager.h>

namespace llvm {
class PassBuilder;
}  // namespace llvm

namespace omill {

/// Register all omill analysis passes with the given managers.
void registerAnalyses(llvm::FunctionAnalysisManager &FAM);

/// Register omill passes with an LLVM PassBuilder (for plugin support).
void registerPassBuilderCallbacks(llvm::PassBuilder &PB);

}  // namespace omill
