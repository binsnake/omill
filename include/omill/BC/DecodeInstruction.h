#pragma once

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Arch/ArchABI.h"

#include <cstdint>
#include <string>

namespace remill {
class Arch;
class Instruction;
}  // namespace remill

namespace omill {

struct DecodeInstructionStatus {
  bool decoder_succeeded = false;
  bool usable = false;
};

bool DecodeInstruction(const remill::Arch &arch, uint64_t pc,
                       const std::string &inst_bytes,
                       remill::Instruction &instruction);

bool DecodeInstruction(const remill::Arch &arch,
                       const BinaryMemoryMap &memory_map, uint64_t pc,
                       remill::Instruction &instruction);

DecodeInstructionStatus ProbeDecodeInstruction(TargetArch target_arch,
                                               const BinaryMemoryMap &memory_map,
                                               uint64_t pc);

}  // namespace omill
