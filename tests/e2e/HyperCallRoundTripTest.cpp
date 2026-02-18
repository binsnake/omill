#include "LiftAndOptFixture.h"

#include "CompileToNative.h"
#include "X86Disassembler.h"

#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

using namespace omill::test;
using omill::e2e::LiftAndOptFixture;

/// Round-trip tests: build IR → lower hypercalls → compile to native →
/// lift with remill → run omill pipeline → compile again → verify.
class HyperCallRoundTripTest : public LiftAndOptFixture {
 protected:
  /// Build a minimal function containing a single sync hyper call,
  /// run LowerHyperCalls, and compile to native x86-64 bytes.
  NativeCode buildFirstPass(uint32_t hyper_call_id, const char *fn_name) {
    auto &Ctx = context();
    auto M = std::make_unique<llvm::Module>("first_pass", Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    M->setTargetTriple(llvm::Triple("x86_64-pc-windows-msvc"));

    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

    // Declare __remill_sync_hyper_call(State*, Memory*, i32) -> Memory*
    auto *hyper_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i32_ty}, false);
    M->getOrInsertFunction("__remill_sync_hyper_call", hyper_ty);

    // Create lifted function: (ptr, i64, ptr) -> ptr
    auto *fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                      fn_name, *M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);

    auto *state = F->getArg(0);
    auto *mem = F->getArg(2);
    auto *hyper_fn = M->getFunction("__remill_sync_hyper_call");
    auto *mem2 =
        B.CreateCall(hyper_fn, {state, mem, B.getInt32(hyper_call_id)});
    B.CreateRet(mem2);

    // Run LowerHyperCalls.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(omill::LowerRemillIntrinsicsPass(omill::LowerCategories::HyperCalls));

      llvm::PassBuilder PB;
      llvm::LoopAnalysisManager LAM;
      llvm::FunctionAnalysisManager FAM;
      llvm::CGSCCAnalysisManager CGAM;
      llvm::ModuleAnalysisManager MAM;
      PB.registerModuleAnalyses(MAM);
      PB.registerCGSCCAnalyses(CGAM);
      PB.registerFunctionAnalyses(FAM);
      PB.registerLoopAnalyses(LAM);
      PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
      FPM.run(*F, FAM);
    }

    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()))
        << "IR invalid after LowerHyperCalls";

    return compileToNative(*M);
  }

  /// Lift native bytes with remill, run omill pipeline, compile again.
  NativeCode roundTrip(const NativeCode &first, uint64_t base_addr) {
    // Feed the compiled bytes to remill for lifting.
    setCode(first.text.data(), first.text.size(), base_addr);
    traceManager().setBaseAddr(base_addr);

    auto *M = lift();
    EXPECT_NE(M, nullptr) << "Remill lift failed";
    if (!M) return {};

    EXPECT_TRUE(verifyModule()) << "Module invalid after lifting";

    // Run omill pipeline (intrinsic lowering + state optimization).
    omill::PipelineOptions opts;
    opts.lower_intrinsics = true;
    opts.optimize_state = true;
    opts.lower_control_flow = false;
    opts.recover_abi = false;
    optimize(opts);

    EXPECT_TRUE(verifyModule()) << "Module invalid after omill pipeline";

    return compileToNative(*M);
  }
};

// ---------------------------------------------------------------------------
// CPUID round-trip
// ---------------------------------------------------------------------------

TEST_F(HyperCallRoundTripTest, CPUIDSurvivesRoundTrip) {
  // First pass: lower CPUID hyper call → compile to native.
  auto first = buildFirstPass(258, "sub_140001000");
  ASSERT_TRUE(first.ok()) << first.error;

  auto first_insns =
      disassemble(first.text.data(), first.text.size(), first.text_addr);
  ASSERT_TRUE(containsMnemonic(first_insns, ZYDIS_MNEMONIC_CPUID))
      << "First compile should contain cpuid";

  // Round-trip: lift → optimize → recompile.
  auto second = roundTrip(first, 0x140001000);
  ASSERT_TRUE(second.ok()) << second.error;

  auto second_insns =
      disassemble(second.text.data(), second.text.size(), second.text_addr);

  // The round-tripped code should still contain cpuid.
  EXPECT_TRUE(containsMnemonic(second_insns, ZYDIS_MNEMONIC_CPUID))
      << "Round-tripped code should still contain cpuid";
}

// ---------------------------------------------------------------------------
// RDTSC round-trip
// ---------------------------------------------------------------------------

TEST_F(HyperCallRoundTripTest, RDTSCSurvivesRoundTrip) {
  auto first = buildFirstPass(259, "sub_140002000");
  ASSERT_TRUE(first.ok()) << first.error;

  auto first_insns =
      disassemble(first.text.data(), first.text.size(), first.text_addr);
  ASSERT_TRUE(containsMnemonic(first_insns, ZYDIS_MNEMONIC_RDTSC))
      << "First compile should contain rdtsc";

  auto second = roundTrip(first, 0x140002000);
  ASSERT_TRUE(second.ok()) << second.error;

  auto second_insns =
      disassemble(second.text.data(), second.text.size(), second.text_addr);

  EXPECT_TRUE(containsMnemonic(second_insns, ZYDIS_MNEMONIC_RDTSC))
      << "Round-tripped code should still contain rdtsc";
}

// ---------------------------------------------------------------------------
// RDTSCP round-trip
// ---------------------------------------------------------------------------

TEST_F(HyperCallRoundTripTest, RDTSCPSurvivesRoundTrip) {
  auto first = buildFirstPass(260, "sub_140003000");
  ASSERT_TRUE(first.ok()) << first.error;

  auto first_insns =
      disassemble(first.text.data(), first.text.size(), first.text_addr);
  ASSERT_TRUE(containsMnemonic(first_insns, ZYDIS_MNEMONIC_RDTSCP))
      << "First compile should contain rdtscp";

  auto second = roundTrip(first, 0x140003000);
  ASSERT_TRUE(second.ok()) << second.error;

  auto second_insns =
      disassemble(second.text.data(), second.text.size(), second.text_addr);

  EXPECT_TRUE(containsMnemonic(second_insns, ZYDIS_MNEMONIC_RDTSCP))
      << "Round-tripped code should still contain rdtscp";
}

}  // namespace
