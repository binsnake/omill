#include "omill/Analysis/RemillIntrinsicAnalysis.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

llvm::AnalysisKey RemillIntrinsicAnalysis::Key;

RemillIntrinsicInfo RemillIntrinsicAnalysis::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  RemillIntrinsicInfo info;

  // Build or reuse the intrinsic table for this module.
  IntrinsicTable table(*F.getParent());

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      // Check for inline asm volatile barriers (remill's separator pattern).
      // These are empty inline asm strings with side effects.
      if (CI->isInlineAsm()) {
        if (auto *IA = llvm::dyn_cast<llvm::InlineAsm>(CI->getCalledOperand())) {
          if (IA->getAsmString().empty() && IA->hasSideEffects()) {
            info.volatile_barriers.push_back(CI);
          }
        }
        continue;
      }

      auto kind = table.classifyCall(CI);
      auto cat = IntrinsicTable::categoryOf(kind);

      switch (cat) {
        case IntrinsicCategory::kMemoryRead:
          info.read_memory.push_back(CI);
          break;
        case IntrinsicCategory::kMemoryWrite:
          info.write_memory.push_back(CI);
          break;
        case IntrinsicCategory::kFlag:
          info.flag_computations.push_back(CI);
          break;
        case IntrinsicCategory::kComparison:
          info.comparisons.push_back(CI);
          break;
        case IntrinsicCategory::kUndefined:
          info.undefined_values.push_back(CI);
          break;
        case IntrinsicCategory::kControlFlow:
          info.control_flow.push_back(CI);
          break;
        case IntrinsicCategory::kHyperCall:
          info.hyper_calls.push_back(CI);
          break;
        case IntrinsicCategory::kBarrier:
          info.barriers.push_back(CI);
          break;
        case IntrinsicCategory::kAtomic:
          info.atomics.push_back(CI);
          break;
        case IntrinsicCategory::kFetchAndOp:
          info.fetch_and_ops.push_back(CI);
          break;
        case IntrinsicCategory::kDelaySlot:
          info.delay_slots.push_back(CI);
          break;
        case IntrinsicCategory::kFPU:
          info.fpu_ops.push_back(CI);
          break;
        case IntrinsicCategory::kIOPort:
          info.io_ports.push_back(CI);
          break;
        case IntrinsicCategory::kX86Specific:
          info.x86_specific.push_back(CI);
          break;
        case IntrinsicCategory::kUnknown:
          break;
      }
    }
  }

  return info;
}

}  // namespace omill
