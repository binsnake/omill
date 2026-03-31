#pragma once

#include <llvm/IR/PassManager.h>

namespace omill {

/// Inlines VM handler functions at indirect dispatch sites.
///
/// VM-based obfuscators (VMProtect, Themida, custom) implement virtual machines
/// where a dispatcher loop reads opcodes and calls handler functions.  In
/// lifted code, these appear as:
///
///   1. A loop containing an indirect call/jump through a handler table
///   2. Handler functions that are small (< threshold instruction count)
///   3. Multiple call sites to the same set of handlers
///
/// This pass identifies functions called from unresolved dispatch call/jump
/// sites or indirect calls within loops, and marks
/// small handler functions with alwaysinline.  It then runs LLVM's
/// AlwaysInliner to perform the actual inlining.
///
/// After inlining, handler bodies are exposed to the full optimization
/// pipeline (GVN, InstCombine, ADCE, CFF unflattening), enabling
/// collapse of the interpreter loop into direct operations.
///
/// Configuration:
///   - max_handler_instructions: maximum handler size to inline (default: 200)
///   - max_handler_callsites: minimum callsite count to be considered a
///     handler (default: 2)
class VMHandlerInlinerPass
    : public llvm::PassInfoMixin<VMHandlerInlinerPass> {
 public:
  explicit VMHandlerInlinerPass(unsigned max_handler_instrs = 200,
                                unsigned min_callsites = 2)
      : max_handler_instrs_(max_handler_instrs),
        min_callsites_(min_callsites) {}

  llvm::PreservedAnalyses run(llvm::Module &M,
                              llvm::ModuleAnalysisManager &MAM);

  static llvm::StringRef name() { return "VMHandlerInlinerPass"; }

 private:
  unsigned max_handler_instrs_;
  unsigned min_callsites_;
};

}  // namespace omill
