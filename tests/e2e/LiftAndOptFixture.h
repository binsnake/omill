#pragma once

#include <llvm/ADT/ArrayRef.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <remill/Arch/Arch.h>
#include <remill/Arch/Name.h>
#include <remill/BC/TraceLifter.h>
#include <remill/BC/Util.h>
#include <remill/OS/OS.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Omill.h"

#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_map>
#include <vector>

namespace omill::e2e {

/// A TraceManager implementation that reads from an in-memory byte buffer.
class BufferTraceManager : public remill::TraceManager {
 public:
  void setCode(const uint8_t *data, size_t size, uint64_t base) {
    code_.clear();
    for (size_t i = 0; i < size; ++i) {
      code_[base + i] = data[i];
    }
    base_addr_ = base;
  }

  /// Append bytes without clearing existing code (for multi-function loading).
  void addCode(const uint8_t *data, size_t size, uint64_t base) {
    for (size_t i = 0; i < size; ++i) {
      code_[base + i] = data[i];
    }
  }

  void SetLiftedTraceDefinition(uint64_t addr,
                                llvm::Function *func) override {
    traces_[addr] = func;
  }

  bool TryReadExecutableByte(uint64_t addr, uint8_t *byte) override {
    auto it = code_.find(addr);
    if (it != code_.end()) {
      *byte = it->second;
      return true;
    }
    return false;
  }

  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr) override {
    auto it = traces_.find(addr);
    return (it != traces_.end()) ? it->second : nullptr;
  }

  llvm::Function *GetLiftedTraceDefinition(uint64_t addr) override {
    return GetLiftedTraceDeclaration(addr);
  }

  const std::unordered_map<uint64_t, llvm::Function *> &traces() const {
    return traces_;
  }

  uint64_t baseAddr() const { return base_addr_; }

  void setBaseAddr(uint64_t addr) { base_addr_ = addr; }

 private:
  std::unordered_map<uint64_t, uint8_t> code_;
  std::unordered_map<uint64_t, llvm::Function *> traces_;
  uint64_t base_addr_ = 0;
};

/// GTest fixture for e2e tests that lifts raw x86_64 bytes with remill
/// and then runs the omill optimization pipeline.
class LiftAndOptFixture : public ::testing::Test {
 protected:
  void SetUp() override;

  /// Load code bytes into the trace manager.
  void setCode(const uint8_t *data, size_t size, uint64_t base);

  /// Lift the code at the base address using remill's TraceLifter.
  /// Returns the module containing lifted IR.
  llvm::Module *lift();

  /// Lift code at the base address plus additional addresses (e.g. handler VAs).
  llvm::Module *liftMultiple(llvm::ArrayRef<uint64_t> addrs);

  /// Run the omill pipeline on the module.
  void optimize(const PipelineOptions &opts = {});

  /// Run the pipeline with a pre-populated BinaryMemoryMap (for deobfuscation).
  void optimizeWithMemoryMap(const PipelineOptions &opts,
                             BinaryMemoryMap memory_map);

  /// Run the pipeline with both a BinaryMemoryMap and ExceptionInfo.
  void optimizeWithExceptions(const PipelineOptions &opts,
                              ExceptionInfo exc_info,
                              BinaryMemoryMap memory_map);

  /// Verify the module is well-formed.
  bool verifyModule();

  /// Dump the current module IR to a file.
  /// Output path: <dir>/<TestSuite>_<TestName>_<tag>.ll
  /// Only writes when OMILL_DUMP_IR env var is set.
  void dumpIR(llvm::StringRef tag);

  /// Access the LLVM context.
  llvm::LLVMContext &context() { return ctx_; }

  /// Access the lifted module.
  llvm::Module *module() { return module_.get(); }

  /// Access the trace manager.
  BufferTraceManager &traceManager() { return manager_; }

 private:
  /// Returns the dump directory from OMILL_DUMP_IR, or empty if not set.
  static std::string getDumpDir();

  llvm::LLVMContext ctx_;
  std::unique_ptr<const remill::Arch> arch_;
  std::unique_ptr<llvm::Module> module_;
  BufferTraceManager manager_;
};

}  // namespace omill::e2e
