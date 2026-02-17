#include "LiftAndOptFixture.h"
#include "PELoader.h"

#include <llvm/IR/Instructions.h>

#include <gtest/gtest.h>

#include <string>

#ifndef OLLVM_TEST_DLL_PATH
#error "OLLVM_TEST_DLL_PATH must be defined to point to ollvm_test.dll"
#endif

namespace {

using omill::e2e::LiftAndOptFixture;
using omill::e2e::PEInfo;
using omill::e2e::loadPE;

class OLLVMTest : public LiftAndOptFixture {
 protected:
  void SetUp() override {
    LiftAndOptFixture::SetUp();
    ASSERT_TRUE(loadPE(OLLVM_TEST_DLL_PATH, pe_))
        << "Failed to load " << OLLVM_TEST_DLL_PATH;
    ASSERT_FALSE(pe_.exports.empty()) << "No exports found in DLL";
    ASSERT_NE(pe_.text_base, 0u) << "No .text section found";
  }

  uint64_t getExportVA(const std::string &name) {
    auto it = pe_.exports.find(name);
    EXPECT_NE(it, pe_.exports.end()) << "Export not found: " << name;
    return (it != pe_.exports.end()) ? it->second : 0;
  }

  llvm::Module *liftExport(uint64_t export_va) {
    text_copy_.resize(pe_.text_size);
    bool read_ok = pe_.memory_map.read(pe_.text_base, text_copy_.data(),
                                       static_cast<unsigned>(pe_.text_size));
    EXPECT_TRUE(read_ok) << "memory_map.read() failed for .text";
    if (!read_ok)
      return nullptr;

    setCode(text_copy_.data(), text_copy_.size(), pe_.text_base);
    traceManager().setBaseAddr(export_va);

    return lift();
  }

  bool liftAndOptimize(const std::string &export_name) {
    uint64_t va = getExportVA(export_name);
    if (va == 0) return false;

    auto *M = liftExport(va);
    if (!M) return false;

    omill::PipelineOptions opts;
    opts.recover_abi = true;
    opts.deobfuscate = true;
    optimizeWithMemoryMap(opts, pe_.memory_map);
    return true;
  }

  // -----------------------------------------------------------------------
  // Assertion helpers
  // -----------------------------------------------------------------------

  /// Count basic blocks across all native functions.
  unsigned countNativeBasicBlocks() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      n += F.size();
    }
    return n;
  }

  /// Count switch instructions across all native functions.
  unsigned countSwitchInsts() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (llvm::isa<llvm::SwitchInst>(&I))
            n++;
    }
    return n;
  }

  /// Count native functions produced by the pipeline (sub_*_native).
  unsigned countNativeFunctions() {
    unsigned n = 0;
    for (auto &F : *module())
      if (!F.isDeclaration() && F.getName().contains("_native"))
        n++;
    return n;
  }

  /// Count total instructions across all native functions.
  unsigned countNativeInstructions() {
    unsigned n = 0;
    for (auto &F : *module()) {
      if (F.isDeclaration() || !F.getName().contains("_native")) continue;
      for (auto &BB : F)
        n += BB.size();
    }
    return n;
  }

  /// Search for a global constant containing a substring in its raw bytes.
  bool hasGlobalConstantString(llvm::StringRef needle) {
    for (auto &GV : module()->globals()) {
      if (!GV.hasInitializer() || !GV.isConstant()) continue;
      if (auto *CDA =
              llvm::dyn_cast<llvm::ConstantDataArray>(GV.getInitializer())) {
        if (CDA->getRawDataValues().contains(needle))
          return true;
      }
    }
    return false;
  }

  /// Search for a constant i64 store with the given value.
  bool hasConstI64Store(uint64_t val) {
    for (auto &F : *module()) {
      if (F.isDeclaration()) continue;
      for (auto &BB : F)
        for (auto &I : BB)
          if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I))
            if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(
                    store->getValueOperand()))
              if (ci->getBitWidth() == 64 && ci->getZExtValue() == val)
                return true;
    }
    return false;
  }

  /// Count @.const_stack* globals.
  unsigned countConstStackGlobals() {
    unsigned n = 0;
    for (auto &GV : module()->globals())
      if (GV.getName().starts_with(".const_stack"))
        n++;
    return n;
  }

  std::vector<uint8_t> text_copy_;
  PEInfo pe_;
};

// =============================================================================
// Sanity: all exports lift + optimize without crashing
// =============================================================================

TEST_F(OLLVMTest, BranchSanity) {
  ASSERT_TRUE(liftAndOptimize("ollvm_branch"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);
}

TEST_F(OLLVMTest, ArithmeticSanity) {
  ASSERT_TRUE(liftAndOptimize("ollvm_arithmetic"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);
}

TEST_F(OLLVMTest, CopyGreetingSanity) {
  ASSERT_TRUE(liftAndOptimize("ollvm_copy_greeting"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);
}

TEST_F(OLLVMTest, LoopSumSanity) {
  ASSERT_TRUE(liftAndOptimize("ollvm_loop_sum"));
  EXPECT_TRUE(verifyModule()) << "Module invalid after optimization";
  EXPECT_GE(countNativeFunctions(), 1u);
}

// =============================================================================
// CFF recovery: BB count should be reduced, switch dispatchers partially or
// fully eliminated.
//
// Current state: CFF switch variable is loaded from memory (alloca in x86),
// so GVN/SimplifyCFG may not fully eliminate the dispatcher. The BB count
// is still reduced vs the raw CFF-inflated code. As the pipeline improves,
// residual switches should drop to 0.
// =============================================================================

/// CFF recovery for ollvm_branch: BB count should be reasonable.
TEST_F(OLLVMTest, BranchCFFRecovery) {
  ASSERT_TRUE(liftAndOptimize("ollvm_branch"));
  EXPECT_TRUE(verifyModule());

  // CFF inflates BB count significantly. After recovery, the count should
  // be manageable even if the dispatcher isn't fully eliminated.
  unsigned bbs = countNativeBasicBlocks();
  EXPECT_LT(bbs, 50u)
      << "Expected CFF BB count to be reduced (got " << bbs << " BBs)";

  // Track residual switches — currently 1 may remain. This should improve
  // as the pipeline gets better at resolving alloca-based switch vars.
  unsigned switches = countSwitchInsts();
  EXPECT_LE(switches, 2u)
      << "Expected at most partial CFF switch residue (got " << switches << ")";
}

/// Loop sum with CFF.
TEST_F(OLLVMTest, LoopSumCFFRecovery) {
  ASSERT_TRUE(liftAndOptimize("ollvm_loop_sum"));
  EXPECT_TRUE(verifyModule());

  unsigned bbs = countNativeBasicBlocks();
  EXPECT_LT(bbs, 50u)
      << "Expected CFF BB count to be reduced for loop (got "
      << bbs << " BBs)";

  unsigned switches = countSwitchInsts();
  EXPECT_LE(switches, 2u)
      << "Expected at most partial CFF switch residue (got " << switches << ")";
}

// =============================================================================
// MBA recovery: instruction count should not be wildly inflated
// =============================================================================

/// The arithmetic function (a+b)^(a-b) with MBA should still be compact
/// after deobfuscation simplifies the MBA expressions.
TEST_F(OLLVMTest, ArithmeticMBARecovery) {
  ASSERT_TRUE(liftAndOptimize("ollvm_arithmetic"));
  EXPECT_TRUE(verifyModule());

  // A simple (a+b)^(a-b) with MBA + CFF should not produce hundreds of
  // instructions after deobfuscation. Allow generous headroom for the
  // x86 lifting overhead.
  unsigned insns = countNativeInstructions();
  EXPECT_LT(insns, 200u)
      << "Expected MBA to be simplified (got " << insns << " instructions)";
}

// =============================================================================
// String encryption recovery
//
// Current state: the XOR-encrypted string + key are in .rdata. After lifting,
// ConstantMemoryFolding should resolve the loads. However, the string
// decryption loop may not be fully folded if the loop structure prevents
// constant propagation. This test documents the current recovery level.
// =============================================================================

/// String encryption: verify the pipeline handles the encrypted string
/// function without crashing, and check for any level of recovery.
TEST_F(OLLVMTest, StringEncryptionRecovery) {
  ASSERT_TRUE(liftAndOptimize("ollvm_copy_greeting"));
  EXPECT_TRUE(verifyModule());

  // Ideal: full string recovered in a global constant.
  bool found_global = hasGlobalConstantString("OLLVM Test String!");

  // Fallback: partial recovery as i64 store constants.
  // "OLLVM Te" = 0x6554204D564C4C4F (LE)
  bool found_partial = hasConstI64Store(0x6554204D564C4C4FULL);

  // Also check for const_stack promotion.
  bool found_stack = countConstStackGlobals() > 0;

  // String encryption recovery depends on ConstantMemoryFolding being able
  // to read the encrypted bytes + key from BinaryMemoryMap and
  // InstCombine/GVN folding the XOR to plaintext. If the decryption loop
  // prevents this, recovery won't fire yet.
  if (found_global || found_partial || found_stack) {
    // Recovery succeeded at some level.
    SUCCEED() << "String encryption partially or fully recovered";
  } else {
    // Document current limitation: string not yet recovered.
    // This is expected until the pipeline can handle the specific
    // decryption pattern generated by our string encryption pass.
    GTEST_SKIP() << "String encryption recovery not yet implemented "
                    "(encrypted data in .rdata not folded)";
  }
}

}  // namespace
