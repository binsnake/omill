#include "omill/Passes/LowerHyperCalls.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>
#include <llvm/TargetParser/Triple.h>

#include "CompileToNative.h"
#include "X86Disassembler.h"

#include <gtest/gtest.h>

namespace {

using namespace omill::test;

class HyperCallCodegenTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with x86-64 data layout.
  std::unique_ptr<llvm::Module> createModule(const char *name) {
    auto M = std::make_unique<llvm::Module>(name, Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    M->setTargetTriple(llvm::Triple("x86_64-pc-windows-msvc"));
    return M;
  }

  /// Create a lifted function signature: (ptr, i64, ptr) -> ptr.
  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  /// Build a function containing a single __remill_sync_hyper_call with the
  /// given ID, run LowerHyperCalls, then compile to native x86-64.
  NativeCode buildAndCompileHyperCall(uint32_t hyper_call_id,
                                       const char *fn_name) {
    auto M = createModule("codegen_test");

    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i32_ty = llvm::Type::getInt32Ty(Ctx);

    // Declare __remill_sync_hyper_call(State*, Memory*, i32) -> Memory*
    auto *hyper_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i32_ty}, false);
    M->getOrInsertFunction("__remill_sync_hyper_call", hyper_ty);

    // Create test function.
    auto *F = llvm::Function::Create(liftedFnType(),
                                      llvm::Function::ExternalLinkage,
                                      fn_name, *M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);

    auto *state = F->getArg(0);
    auto *mem = F->getArg(2);
    auto *hyper_fn = M->getFunction("__remill_sync_hyper_call");
    auto *mem2 =
        B.CreateCall(hyper_fn, {state, mem, B.getInt32(hyper_call_id)});
    B.CreateRet(mem2);

    // Run LowerHyperCalls pass.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(omill::LowerHyperCallsPass());

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

    // Verify IR before codegen.
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

    return compileToNative(*M);
  }
};

// ---------------------------------------------------------------------------
// CPUID codegen
// ---------------------------------------------------------------------------

TEST_F(HyperCallCodegenTest, CPUIDEmitsCpuidInstruction) {
  auto code = buildAndCompileHyperCall(258, "test_cpuid");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);
  ASSERT_FALSE(insns.empty());

  // Must contain a cpuid instruction.
  EXPECT_TRUE(containsMnemonic(insns, ZYDIS_MNEMONIC_CPUID))
      << "Expected cpuid instruction in codegen output";

  // Should NOT contain a call to an external stub — CPUID is fully inlined.
  // A 'call' to an external symbol would appear as CALL with a RIP-relative
  // operand.  We allow calls that are part of inline asm, but there should be
  // no call to __omill_sync_hyper_call.
  // (We can't check symbol names in the disassembly, but we verify at IR level
  //  in the existing unit test.)
}

TEST_F(HyperCallCodegenTest, CPUIDAccessesStateAtCorrectOffsets) {
  auto code = buildAndCompileHyperCall(258, "test_cpuid_offsets");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);

  // CPUID reads EAX (State+2216) and ECX (State+2248) before the cpuid,
  // and writes EAX, EBX (State+2232), ECX, EDX (State+2264) after.
  // The codegen should contain mov instructions referencing these offsets
  // from the State pointer (RCX in Win64 ABI, first arg).
  //
  // Look for the key offsets in the disassembly text.
  // State+2216 = 0x8A8, State+2232 = 0x8B8, State+2248 = 0x8C8,
  // State+2264 = 0x8D8.
  bool found_eax_offset = false;  // 0x8A8
  bool found_ebx_offset = false;  // 0x8B8
  bool found_ecx_offset = false;  // 0x8C8
  bool found_edx_offset = false;  // 0x8D8

  for (auto &insn : insns) {
    if (insn.text.find("0x8A8") != std::string::npos ||
        insn.text.find("0x8a8") != std::string::npos)
      found_eax_offset = true;
    if (insn.text.find("0x8B8") != std::string::npos ||
        insn.text.find("0x8b8") != std::string::npos)
      found_ebx_offset = true;
    if (insn.text.find("0x8C8") != std::string::npos ||
        insn.text.find("0x8c8") != std::string::npos)
      found_ecx_offset = true;
    if (insn.text.find("0x8D8") != std::string::npos ||
        insn.text.find("0x8d8") != std::string::npos)
      found_edx_offset = true;
  }

  EXPECT_TRUE(found_eax_offset)
      << "Expected State+0x8A8 (EAX) access in cpuid codegen";
  EXPECT_TRUE(found_ebx_offset)
      << "Expected State+0x8B8 (EBX) access in cpuid codegen";
  EXPECT_TRUE(found_ecx_offset)
      << "Expected State+0x8C8 (ECX) access in cpuid codegen";
  EXPECT_TRUE(found_edx_offset)
      << "Expected State+0x8D8 (EDX) access in cpuid codegen";
}

// ---------------------------------------------------------------------------
// RDTSC codegen
// ---------------------------------------------------------------------------

TEST_F(HyperCallCodegenTest, RDTSCEmitsRdtscInstruction) {
  auto code = buildAndCompileHyperCall(259, "test_rdtsc");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);
  ASSERT_FALSE(insns.empty());

  EXPECT_TRUE(containsMnemonic(insns, ZYDIS_MNEMONIC_RDTSC))
      << "Expected rdtsc instruction in codegen output";
}

TEST_F(HyperCallCodegenTest, RDTSCStoresEAXAndEDX) {
  auto code = buildAndCompileHyperCall(259, "test_rdtsc_stores");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);

  // RDTSC writes low 32 bits to EAX (State+0x8A8) and high 32 to EDX
  // (State+0x8D8).
  bool found_eax_offset = false;
  bool found_edx_offset = false;

  for (auto &insn : insns) {
    if (insn.text.find("0x8A8") != std::string::npos ||
        insn.text.find("0x8a8") != std::string::npos)
      found_eax_offset = true;
    if (insn.text.find("0x8D8") != std::string::npos ||
        insn.text.find("0x8d8") != std::string::npos)
      found_edx_offset = true;
  }

  EXPECT_TRUE(found_eax_offset)
      << "Expected State+0x8A8 (EAX) store in rdtsc codegen";
  EXPECT_TRUE(found_edx_offset)
      << "Expected State+0x8D8 (EDX) store in rdtsc codegen";
}

// ---------------------------------------------------------------------------
// RDTSCP codegen
// ---------------------------------------------------------------------------

TEST_F(HyperCallCodegenTest, RDTSCPEmitsRdtscpInstruction) {
  auto code = buildAndCompileHyperCall(260, "test_rdtscp");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);
  ASSERT_FALSE(insns.empty());

  EXPECT_TRUE(containsMnemonic(insns, ZYDIS_MNEMONIC_RDTSCP))
      << "Expected rdtscp instruction in codegen output";
}

TEST_F(HyperCallCodegenTest, RDTSCPStoresAllThreeRegisters) {
  auto code = buildAndCompileHyperCall(260, "test_rdtscp_stores");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);

  // RDTSCP writes EAX (0x8A8), EDX (0x8D8), ECX (0x8C8).
  bool found_eax = false, found_ecx = false, found_edx = false;

  for (auto &insn : insns) {
    if (insn.text.find("0x8A8") != std::string::npos ||
        insn.text.find("0x8a8") != std::string::npos)
      found_eax = true;
    if (insn.text.find("0x8C8") != std::string::npos ||
        insn.text.find("0x8c8") != std::string::npos)
      found_ecx = true;
    if (insn.text.find("0x8D8") != std::string::npos ||
        insn.text.find("0x8d8") != std::string::npos)
      found_edx = true;
  }

  EXPECT_TRUE(found_eax)
      << "Expected State+0x8A8 (EAX) store in rdtscp codegen";
  EXPECT_TRUE(found_ecx)
      << "Expected State+0x8C8 (ECX) store in rdtscp codegen";
  EXPECT_TRUE(found_edx)
      << "Expected State+0x8D8 (EDX) store in rdtscp codegen";
}

// ---------------------------------------------------------------------------
// Win64 ABI conformance
// ---------------------------------------------------------------------------

TEST_F(HyperCallCodegenTest, CPUIDFollowsWin64ABI) {
  auto code = buildAndCompileHyperCall(258, "test_cpuid_abi");
  ASSERT_TRUE(code.ok()) << code.error;

  auto insns = disassemble(code.text.data(), code.text.size(), code.text_addr);
  ASSERT_FALSE(insns.empty());

  // Win64 ABI: function must end with ret.
  EXPECT_EQ(insns.back().mnemonic, ZYDIS_MNEMONIC_RET)
      << "Function should end with ret";

  // CPUID clobbers EBX which is non-volatile in Win64.  The codegen must
  // save and restore it (push rbx ... pop rbx, or mov to stack).
  // Check for push rbx or a mov [rsp+...], rbx style save.
  bool saves_rbx = false;
  for (auto &insn : insns) {
    // push rbx
    if (insn.mnemonic == ZYDIS_MNEMONIC_PUSH &&
        insn.text.find("rbx") != std::string::npos)
      saves_rbx = true;
    // mov [rsp+...], rbx
    if (insn.mnemonic == ZYDIS_MNEMONIC_MOV &&
        insn.text.find("rbx") != std::string::npos &&
        insn.text.find("rsp") != std::string::npos)
      saves_rbx = true;
  }
  EXPECT_TRUE(saves_rbx)
      << "CPUID clobbers EBX (non-volatile in Win64) — must be saved";
}

}  // namespace
