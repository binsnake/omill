#pragma once

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/PassManager.h>

namespace llvm {
class Function;
class Module;
}  // namespace llvm

namespace omill {

/// Detected calling convention for a lifted function.
enum class DetectedCC {
  kUnknown,
  kWin64,          // RCX, RDX, R8, R9; RAX return; 32-byte shadow space
};

/// Describes a recovered function parameter.
struct RecoveredParam {
  std::string reg_name;   // Source register (e.g. "RDI", "RCX")
  unsigned state_offset;  // Byte offset in State struct
  unsigned size;          // Size in bytes (typically 8 for GPR)
  unsigned index;         // Parameter index (0-based)
};

/// Describes the recovered return value.
struct RecoveredReturn {
  std::string reg_name;   // Typically "RAX" or "XMM0"
  unsigned state_offset;
  unsigned size;
  bool is_vector = false; // True for XMM0 (<2 x i64>) returns
};

/// Describes a stack-passed parameter (5th+ in Win64).
struct RecoveredStackParam {
  int64_t stack_offset;   // Offset from caller RSP (e.g., 0x28 for 5th arg)
  unsigned size;          // Size in bytes (typically 8)
  unsigned index;         // Overall parameter index (4-based for Win64)
};

/// Per-function calling convention analysis result.
struct FunctionABI {
  DetectedCC cc = DetectedCC::kUnknown;

  /// Parameters in calling convention order.
  llvm::SmallVector<RecoveredParam, 6> params;

  /// Return value info (empty if void).
  std::optional<RecoveredReturn> ret;

  /// The set of callee-saved registers that this function modifies
  /// (and must therefore save/restore, or that we know are preserved).
  llvm::SmallVector<std::string, 8> clobbered_callee_saved;

  /// Win64 shadow space (home area) size in bytes. Always 32 for Win64.
  unsigned shadow_space_size = 0;

  /// True if the function has non-standard register usage (e.g. XMM live-ins)
  /// that can't be modeled by the detected calling convention.
  bool has_non_standard_regs = false;

  /// XMM register live-ins (byte offsets into State) that need to be passed
  /// as extra <2 x i64> parameters after the GPR params.
  llvm::SmallVector<unsigned, 4> xmm_live_ins;

  /// Stack-passed parameters (5th+ in Win64), detected from callsite analysis.
  llvm::SmallVector<RecoveredStackParam, 4> stack_params;

  /// Extra GPR live-ins that are NOT standard Win64 params (callee-saved regs
  /// like RBX, RSI, R14 that the function reads before writing).  These are
  /// passed as extra i64 parameters after XMM params.
  llvm::SmallVector<unsigned, 8> extra_gpr_live_ins;


  /// Extra GPR live-outs: State offsets of callee-saved registers that the
  /// function clobbers (writes without restoring).  These are returned as
  /// additional i64 values packed into a struct return alongside the primary
  /// return value.  At call sites the caller stores them back into State so
  /// that interprocedural register flow is preserved.
  llvm::SmallVector<unsigned, 4> extra_gpr_live_outs;
  bool isVoid() const { return !ret.has_value(); }
  unsigned numParams() const { return params.size(); }
  unsigned numXMMParams() const { return xmm_live_ins.size(); }
  unsigned numExtraGPRParams() const { return extra_gpr_live_ins.size(); }
  unsigned numExtraGPRReturns() const { return extra_gpr_live_outs.size(); }
  unsigned numStackParams() const { return stack_params.size(); }
  unsigned totalNativeParams() const {
    return numParams() + numStackParams() + numXMMParams() +
           numExtraGPRParams();
  }
  bool hasStructReturn() const {
    return !extra_gpr_live_outs.empty();
  }
};

/// Module-level analysis result mapping each lifted function to its ABI.
struct CallingConventionInfo {
  llvm::DenseMap<const llvm::Function *, FunctionABI> function_abis;

  const FunctionABI *getABI(const llvm::Function *F) const {
    auto it = function_abis.find(F);
    return it != function_abis.end() ? &it->second : nullptr;
  }
};

/// Module-level analysis that determines per-function calling conventions
/// by examining live-in/live-out State fields and matching against known
/// x86_64 ABIs (SysV and Win64).
class CallingConventionAnalysis
    : public llvm::AnalysisInfoMixin<CallingConventionAnalysis> {
  friend llvm::AnalysisInfoMixin<CallingConventionAnalysis>;
  static llvm::AnalysisKey Key;

 public:
  using Result = CallingConventionInfo;

  Result run(llvm::Module &M, llvm::ModuleAnalysisManager &MAM);
};

}  // namespace omill
