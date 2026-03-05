#include "omill/Arch/ArchABI.h"

namespace omill {

ArchABI ArchABI::getWin64ABI() {
  ArchABI abi;
  abi.arch = TargetArch::kX86_64;
  abi.os_name = "windows";
  abi.param_regs = {"RCX", "RDX", "R8", "R9"};
  abi.fp_param_regs = {"XMM0", "XMM1", "XMM2", "XMM3"};
  abi.callee_saved = {"RBX", "RBP", "RDI", "RSI",
                      "R12", "R13", "R14", "R15"};
  abi.stack_pointer = "RSP";
  abi.program_counter = "RIP";
  abi.return_reg = "RAX";
  abi.vec_return_reg = "XMM0";
  abi.shadow_space = 32;
  abi.red_zone = 0;
  abi.stack_alignment = 16;
  abi.volatile_scratch = {"RAX", "R10", "R11"};
  abi.max_vec_params = 4;
  abi.position_based_params = true;
  return abi;
}

ArchABI ArchABI::getAAPCS64DarwinABI() {
  ArchABI abi;
  abi.arch = TargetArch::kAArch64;
  abi.os_name = "darwin";
  abi.param_regs = {"X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"};
  abi.fp_param_regs = {"V0", "V1", "V2", "V3", "V4", "V5", "V6", "V7"};
  abi.callee_saved = {"X19", "X20", "X21", "X22", "X23", "X24",
                      "X25", "X26", "X27", "X28", "FP", "LR"};
  abi.stack_pointer = "SP";
  abi.program_counter = "PC";
  abi.return_reg = "X0";
  abi.vec_return_reg = "V0";
  abi.shadow_space = 0;
  abi.red_zone = 128;
  abi.stack_alignment = 16;
  abi.volatile_scratch = {"X9", "X10", "X11", "X12", "X13",
                          "X14", "X15", "X16", "X17", "X18"};
  abi.max_vec_params = 8;
  abi.position_based_params = false;
  return abi;
}

ArchABI ArchABI::getAAPCS64LinuxABI() {
  ArchABI abi = getAAPCS64DarwinABI();
  abi.os_name = "linux";
  abi.red_zone = 0;
  // X18 is reserved as platform register on Linux (TLS).
  // Remove from volatile scratch, add to callee_saved conceptually.
  // In practice, lifted code shouldn't touch X18 at all.
  return abi;
}

ArchABI ArchABI::get(TargetArch arch, llvm::StringRef os) {
  if (arch == TargetArch::kAArch64) {
    if (os.contains("darwin") || os.contains("macos") || os.contains("ios"))
      return getAAPCS64DarwinABI();
    return getAAPCS64LinuxABI();
  }
  // Default: x86_64 / Win64
  return getWin64ABI();
}

}  // namespace omill
