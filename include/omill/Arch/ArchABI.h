#pragma once

#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>

#include <string>

namespace omill {

/// Target architecture for lifted code.
enum class TargetArch {
  kX86_64,
  kAArch64,
};

/// ABI descriptor for a target architecture + OS combination.
/// Contains the register names, calling convention details, and
/// stack layout information needed by the pipeline passes.
struct ArchABI {
  TargetArch arch;
  std::string os_name;  // "windows", "darwin", "linux"

  /// Integer/pointer parameter registers, in order.
  llvm::SmallVector<std::string, 8> param_regs;

  /// Floating-point/vector parameter registers, in order.
  llvm::SmallVector<std::string, 8> fp_param_regs;

  /// Callee-saved (nonvolatile) registers.
  llvm::SmallVector<std::string, 16> callee_saved;

  /// Stack pointer register name.
  std::string stack_pointer;

  /// Program counter register name.
  std::string program_counter;

  /// Primary integer return register.
  std::string return_reg;

  /// Primary vector/FP return register.
  std::string vec_return_reg;

  /// Shadow space (home area) size in bytes. Win64 = 32, AAPCS64 = 0.
  unsigned shadow_space = 0;

  /// Red zone size in bytes. SysV x86_64 = 128, AAPCS64 Darwin = 128,
  /// AAPCS64 Linux = 0.
  unsigned red_zone = 0;

  /// Required stack alignment in bytes.
  unsigned stack_alignment = 16;

  /// Volatile scratch registers (not params, not callee-saved, excluded from
  /// extra-GPR analysis).
  llvm::SmallVector<std::string, 8> volatile_scratch;

  /// Maximum number of vector parameter registers.
  unsigned max_vec_params = 4;

  /// Whether this ABI uses the Win64-style position-based register assignment
  /// (GPR and XMM share slot indices) vs AAPCS64/SysV independent counters.
  bool position_based_params = true;

  // --- Factories ---

  /// Win64 ABI: RCX, RDX, R8, R9; 32-byte shadow space.
  static ArchABI getWin64ABI();

  /// AAPCS64 for Darwin (macOS/iOS): X0-X7, D0-D7; 128-byte red zone.
  static ArchABI getAAPCS64DarwinABI();

  /// AAPCS64 for Linux: X0-X7, D0-D7; no red zone.
  static ArchABI getAAPCS64LinuxABI();

  /// Auto-select ABI from arch + OS name.
  /// Falls back to Win64 for x86_64/windows, AAPCS64 Darwin for aarch64/darwin.
  static ArchABI get(TargetArch arch, llvm::StringRef os);
};

}  // namespace omill
