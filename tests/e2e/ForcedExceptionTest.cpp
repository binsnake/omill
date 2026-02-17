#include "LiftAndOptFixture.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>

#include <gtest/gtest.h>

#include <cstring>

namespace {

using omill::e2e::LiftAndOptFixture;

class ForcedExceptionTest : public LiftAndOptFixture {};

/// Helper: check if __remill_error is called anywhere in the module.
static bool hasRemillError(llvm::Module *M) {
  for (auto &F : *M) {
    if (F.isDeclaration()) continue;
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = CI->getCalledFunction())
            if (callee->getName() == "__remill_error")
              return true;
  }
  return false;
}

/// Helper: check if a constant i64 value appears anywhere in the module IR.
static bool hasConstantI64(llvm::Module *M, uint64_t val) {
  for (auto &F : *M) {
    if (F.isDeclaration()) continue;
    for (auto &BB : F)
      for (auto &I : BB)
        for (auto &Op : I.operands())
          if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(Op.get()))
            if (CI->getBitWidth() == 64 && CI->getZExtValue() == val)
              return true;
  }
  return false;
}

/// Test 1: Handler is inlined into the UD2 entry function.
///
/// Entry (0x401000): ud2                          (0F 0B)
/// Handler (0x401100): mov rax, [r9+0x38]; ret    (49 8B 41 38 C3)
///
/// The handler reads HandlerData from DISPATCHER_CONTEXT+0x38.
/// After ResolveForcedExceptions + AlwaysInliner, the handler body
/// should be inlined into the entry function, eliminating __remill_error.
TEST_F(ForcedExceptionTest, HandlerInlined) {
  // Entry: ud2
  static const uint8_t entry_code[] = {0x0F, 0x0B};
  // Handler: mov rax, [r9+0x38]; ret
  static const uint8_t handler_code[] = {0x49, 0x8B, 0x41, 0x38, 0xC3};

  constexpr uint64_t entry_va = 0x401000;
  constexpr uint64_t handler_va = 0x401100;
  constexpr uint64_t handler_data_va = 0x500000;

  // Load both code regions.
  setCode(entry_code, sizeof(entry_code), entry_va);
  traceManager().addCode(handler_code, sizeof(handler_code), handler_va);

  // Lift both entry and handler.
  auto *M = liftMultiple({entry_va, handler_va});
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  // Set up exception info.
  omill::ExceptionInfo exc_info;
  exc_info.setImageBase(0x400000);
  exc_info.addEntry({entry_va, entry_va + 2, handler_va, handler_data_va, 0});

  // Set up memory map with handler data.
  omill::BinaryMemoryMap mem_map;
  uint64_t handler_data_value = 0x12345678AABBCCDDULL;
  mem_map.addRegion(handler_data_va,
                    reinterpret_cast<const uint8_t *>(&handler_data_value),
                    sizeof(handler_data_value));

  // Run pipeline.
  omill::PipelineOptions opts;
  opts.recover_abi = false;
  optimizeWithExceptions(opts, std::move(exc_info), std::move(mem_map));

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";

  // __remill_error should be eliminated (handler was inlined).
  EXPECT_FALSE(hasRemillError(module()))
      << "Expected __remill_error to be eliminated after handler inlining";
}

/// Test 2: Handler reads [R9+0x38] (HandlerData ptr), then dereferences it.
///
/// Entry (0x401000): ud2
/// Handler (0x401100): mov rax, [r9+0x38]; mov rax, [rax]; ret
///   (49 8B 41 38  48 8B 00  C3)
///
/// Memory layout:
///   DC+0x38 = 0x500000 (HandlerData VA)
///   [0x500000] = 0xDEADBEEFCAFEBABE
///
/// After ConstantMemoryFolding, the double-dereference should fold to the
/// constant 0xDEADBEEFCAFEBABE.
TEST_F(ForcedExceptionTest, HandlerDataChainFolded) {
  static const uint8_t entry_code[] = {0x0F, 0x0B};
  // mov rax, [r9+0x38]; mov rax, [rax]; ret
  static const uint8_t handler_code[] = {
      0x49, 0x8B, 0x41, 0x38,  // mov rax, [r9+0x38]
      0x48, 0x8B, 0x00,        // mov rax, [rax]
      0xC3,                    // ret
  };

  constexpr uint64_t entry_va = 0x401000;
  constexpr uint64_t handler_va = 0x401100;
  constexpr uint64_t handler_data_va = 0x500000;

  setCode(entry_code, sizeof(entry_code), entry_va);
  traceManager().addCode(handler_code, sizeof(handler_code), handler_va);

  auto *M = liftMultiple({entry_va, handler_va});
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  omill::ExceptionInfo exc_info;
  exc_info.setImageBase(0x400000);
  exc_info.addEntry({entry_va, entry_va + 2, handler_va, handler_data_va, 0});

  // Memory: HandlerData at 0x500000 contains pointer value 0xDEADBEEFCAFEBABE.
  omill::BinaryMemoryMap mem_map;
  uint64_t folded_value = 0xDEADBEEFCAFEBABEULL;
  mem_map.addRegion(handler_data_va,
                    reinterpret_cast<const uint8_t *>(&folded_value),
                    sizeof(folded_value));

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.interprocedural_const_prop = true;
  optimizeWithExceptions(opts, std::move(exc_info), std::move(mem_map));

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_FALSE(hasRemillError(module()))
      << "Expected __remill_error to be eliminated";

  // The constant 0xDEADBEEFCAFEBABE should appear as a folded value in the IR.
  EXPECT_TRUE(hasConstantI64(module(), 0xDEADBEEFCAFEBABEULL))
      << "Expected folded constant 0xDEADBEEFCAFEBABE in output IR";
}

/// Test 3: Handler reads [R9+0x38] and [R9+0x08], adds them.
///
/// Entry (0x401000): ud2
/// Handler (0x401100):
///   mov rax, [r9+0x38]   ; HandlerData ptr
///   mov rcx, [rax]        ; *HandlerData = 0x1000
///   mov rax, [r9+0x08]    ; ImageBase = 0x140000000
///   add rax, rcx           ; 0x140000000 + 0x1000 = 0x140001000
///   ret
///
/// Encoded: 49 8B 41 38  48 8B 08  49 8B 41 08  48 01 C8  C3
TEST_F(ForcedExceptionTest, HandlerWithComputation) {
  static const uint8_t entry_code[] = {0x0F, 0x0B};
  static const uint8_t handler_code[] = {
      0x49, 0x8B, 0x41, 0x38,  // mov rax, [r9+0x38]
      0x48, 0x8B, 0x08,        // mov rcx, [rax]
      0x49, 0x8B, 0x41, 0x08,  // mov rax, [r9+0x08]
      0x48, 0x01, 0xC8,        // add rax, rcx
      0xC3,                    // ret
  };

  constexpr uint64_t entry_va = 0x401000;
  constexpr uint64_t handler_va = 0x401100;
  constexpr uint64_t handler_data_va = 0x500000;
  constexpr uint64_t image_base = 0x140000000ULL;

  setCode(entry_code, sizeof(entry_code), entry_va);
  traceManager().addCode(handler_code, sizeof(handler_code), handler_va);

  auto *M = liftMultiple({entry_va, handler_va});
  ASSERT_NE(M, nullptr);
  EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

  omill::ExceptionInfo exc_info;
  exc_info.setImageBase(image_base);
  exc_info.addEntry({entry_va, entry_va + 2, handler_va, handler_data_va, 0});

  // Memory: HandlerData at 0x500000 contains RVA 0x1000.
  omill::BinaryMemoryMap mem_map;
  uint64_t rva_value = 0x1000;
  mem_map.addRegion(handler_data_va,
                    reinterpret_cast<const uint8_t *>(&rva_value),
                    sizeof(rva_value));

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.interprocedural_const_prop = true;
  optimizeWithExceptions(opts, std::move(exc_info), std::move(mem_map));

  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_FALSE(hasRemillError(module()))
      << "Expected __remill_error to be eliminated";

  // The sum 0x140000000 + 0x1000 = 0x140001000 should appear as a constant.
  EXPECT_TRUE(hasConstantI64(module(), 0x140001000ULL))
      << "Expected folded constant 0x140001000 (ImageBase + RVA) in output IR";
}

}  // namespace
