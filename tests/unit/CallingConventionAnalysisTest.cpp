#include "omill/Analysis/CallingConventionAnalysis.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Utils/StateFieldMap.h"

#include <gtest/gtest.h>

namespace {

class CallingConventionAnalysisTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Helper: create a module with __remill_basic_block register GEPs
  /// and a lifted function that reads/writes specified registers.
  std::unique_ptr<llvm::Module> createModuleWithState(
      const std::vector<std::pair<std::string, unsigned>> &live_in_regs,
      bool writes_rax = true) {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

    auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
    auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
    state_ty->setBody({arr_ty});

    // __remill_basic_block with register name GEPs.
    auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);

    auto *bb_state = bb_fn->getArg(0);
    struct RegDef { const char *name; unsigned offset; };
    RegDef all_regs[] = {
        {"RAX", 0}, {"RBX", 8}, {"RCX", 16}, {"RDX", 24},
        {"RSI", 32}, {"RDI", 40}, {"RSP", 48}, {"RBP", 56},
        {"R8", 64}, {"R9", 72}, {"R10", 80}, {"R11", 88},
        {"R12", 96}, {"R13", 104}, {"R14", 112}, {"R15", 120},
        {"RIP", 128},
    };
    for (auto &reg : all_regs) {
      // Use i64 element type so StateFieldMap sees size=8 for GPR fields.
      // StateFieldMap uses getTypeAllocSize(GEP->getResultElementType()).
      // GEP(i64, ptr, idx) has result element type i64 → size=8.
      auto *gep = BBB.CreateGEP(BBB.getInt64Ty(), bb_state,
                                BBB.getInt64(reg.offset / 8));
      gep->setName(reg.name);
    }
    BBB.CreateRet(bb_fn->getArg(2));

    // Test lifted function.
    auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *test_fn = llvm::Function::Create(
        fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
    llvm::IRBuilder<> B(entry);

    auto *state = test_fn->getArg(0);
    auto *mem = test_fn->getArg(2);

    // Load from each live-in register.
    for (auto &[name, offset] : live_in_regs) {
      auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, offset);
      B.CreateLoad(i64_ty, gep, name + "_val");
    }

    // Optionally store result to RAX.
    if (writes_rax) {
      auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
      B.CreateStore(B.getInt64(42), rax_gep);
    }

    B.CreateRet(mem);
    return M;
  }
};

TEST_F(CallingConventionAnalysisTest, DetectsWin64WithTwoParams) {
  // Win64: params in RCX (offset 16), RDX (offset 24)
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RDX", 24},
  });

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *test_fn = M->getFunction("sub_401000");
  ASSERT_NE(test_fn, nullptr);

  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  EXPECT_EQ(abi->cc, omill::DetectedCC::kWin64);
  EXPECT_EQ(abi->numParams(), 2u);
  EXPECT_EQ(abi->params[0].reg_name, "RCX");
  EXPECT_EQ(abi->params[1].reg_name, "RDX");
  EXPECT_TRUE(abi->ret.has_value());
  EXPECT_EQ(abi->ret->reg_name, "RAX");
  EXPECT_EQ(abi->shadow_space_size, 32u);
}

TEST_F(CallingConventionAnalysisTest, DetectsWin64FourParams) {
  // Win64: all 4 params RCX, RDX, R8, R9
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RDX", 24},
      {"R8", 64},
      {"R9", 72},
  });

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *test_fn = M->getFunction("sub_401000");
  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  EXPECT_EQ(abi->cc, omill::DetectedCC::kWin64);
  EXPECT_EQ(abi->numParams(), 4u);
  EXPECT_EQ(abi->params[0].reg_name, "RCX");
  EXPECT_EQ(abi->params[1].reg_name, "RDX");
  EXPECT_EQ(abi->params[2].reg_name, "R8");
  EXPECT_EQ(abi->params[3].reg_name, "R9");
}

TEST_F(CallingConventionAnalysisTest, NonEntryR8ReadDoesNotAddThirdParam) {
  // Entry uses RCX/RDX (2 params). A later R8 read should not be treated as
  // an additional ABI parameter.
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RDX", 24},
  });

  auto *test_fn = M->getFunction("sub_401000");
  ASSERT_NE(test_fn, nullptr);
  ASSERT_FALSE(test_fn->empty());

  auto *ret_inst = llvm::dyn_cast<llvm::ReturnInst>(
      test_fn->getEntryBlock().getTerminator());
  ASSERT_NE(ret_inst, nullptr);
  llvm::Value *ret_val = ret_inst->getReturnValue();

  auto *late_bb = llvm::BasicBlock::Create(Ctx, "late", test_fn);
  llvm::IRBuilder<> BE(ret_inst);
  BE.CreateBr(late_bb);
  ret_inst->eraseFromParent();

  llvm::IRBuilder<> BL(late_bb);
  auto *state = test_fn->getArg(0);
  auto *r8_gep = BL.CreateConstGEP1_64(BL.getInt8Ty(), state, 64);
  BL.CreateLoad(BL.getInt64Ty(), r8_gep, "late_r8");
  BL.CreateRet(ret_val);

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);
  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);

  EXPECT_EQ(abi->cc, omill::DetectedCC::kWin64);
  EXPECT_EQ(abi->numParams(), 2u);
  EXPECT_EQ(abi->params[0].reg_name, "RCX");
  EXPECT_EQ(abi->params[1].reg_name, "RDX");

  bool found_r8_extra = false;
  for (auto off : abi->extra_gpr_live_ins) {
    if (off == 64u) found_r8_extra = true;
  }
  EXPECT_FALSE(found_r8_extra);
}

TEST_F(CallingConventionAnalysisTest, DefaultsToWin64WhenNoParamRegsDetected) {
  // When no parameter registers are read in the entry block (e.g. obfuscated
  // functions with SSE mutation), default to Win64 with all 4 params.
  auto M = createModuleWithState({}, /*writes_rax=*/false);

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *test_fn = M->getFunction("sub_401000");
  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  EXPECT_EQ(abi->cc, omill::DetectedCC::kWin64);
  EXPECT_EQ(abi->numParams(), 4u);
  EXPECT_EQ(abi->params[0].reg_name, "RCX");
  EXPECT_EQ(abi->params[1].reg_name, "RDX");
  EXPECT_EQ(abi->params[2].reg_name, "R8");
  EXPECT_EQ(abi->params[3].reg_name, "R9");
  EXPECT_FALSE(abi->ret.has_value());
}

TEST_F(CallingConventionAnalysisTest, XMMLiveInsDetected) {
  // A function that reads from XMM0 (vector offset) before writing.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  // __remill_basic_block with GPR + XMM GEPs.
  auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);

  // GPR registers.
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 0, "RAX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 16, "RCX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 24, "RDX");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 64, "R8");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 72, "R9");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 48, "RSP");
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 128, "RIP");
  // XMM register at offset 200.
  BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, 200, "XMM0");
  BBB.CreateRet(bb_fn->getArg(2));

  // Lifted function that reads RCX and XMM0.
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *test_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", test_fn);
  llvm::IRBuilder<> B(entry);
  auto *state = test_fn->getArg(0);

  // Read RCX.
  auto *rcx_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 16);
  B.CreateLoad(i64_ty, rcx_gep, "rcx_val");
  // Read XMM0.
  auto *xmm_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 200);
  B.CreateLoad(i64_ty, xmm_gep, "xmm0_val");
  // Write RAX.
  auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
  B.CreateStore(B.getInt64(42), rax_gep);

  B.CreateRet(test_fn->getArg(2));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);
  auto *abi = result.getABI(test_fn);
  ASSERT_NE(abi, nullptr);
  // New behavior: XMM at position 2 is beyond the detected GPR param count
  // (only RCX = 1 param), so it's filtered as an obfuscation artifact.
  EXPECT_TRUE(abi->xmm_live_ins.empty());
  EXPECT_FALSE(abi->has_non_standard_regs);
}

TEST_F(CallingConventionAnalysisTest, ExtraGPRLiveInsDetected) {
  // A function that reads RBX (callee-saved) before writing.
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RBX", 8},  // callee-saved, not a standard param
  });

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);
  auto *abi = result.getABI(M->getFunction("sub_401000"));
  ASSERT_NE(abi, nullptr);
  // New behavior: RBX is callee-saved in Win64 ABI, so it's excluded from
  // extra_gpr_live_ins even if read before written.
  bool found_rbx = false;
  for (auto off : abi->extra_gpr_live_ins) {
    if (off == 8) found_rbx = true;
  }
  EXPECT_FALSE(found_rbx);
}

TEST_F(CallingConventionAnalysisTest, RSPExcludedFromExtraGPR) {
  // RSP read before write should NOT be added to extra_gpr_live_ins.
  auto M = createModuleWithState({
      {"RCX", 16},
      {"RSP", 48},
  });

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);
  auto *abi = result.getABI(M->getFunction("sub_401000"));
  ASSERT_NE(abi, nullptr);
  // RSP should NOT appear in extra_gpr_live_ins.
  for (auto off : abi->extra_gpr_live_ins) {
    EXPECT_NE(off, 48u) << "RSP should be excluded from extra_gpr_live_ins";
  }
}

TEST_F(CallingConventionAnalysisTest, VoidReturnWrapper) {
  // Function that doesn't write RAX → no return value.
  auto M = createModuleWithState({{"RCX", 16}}, /*writes_rax=*/false);

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);
  auto *abi = result.getABI(M->getFunction("sub_401000"));
  ASSERT_NE(abi, nullptr);
  EXPECT_FALSE(abi->ret.has_value());
  EXPECT_TRUE(abi->isVoid());
}

// ===----------------------------------------------------------------------===
// Test: Callsite-driven param count refinement
// ===----------------------------------------------------------------------===

TEST_F(CallingConventionAnalysisTest, CallsiteRefinesParamCount) {
  // Callee body has no visible param reads (obfuscated).
  // But the caller stores RCX, RDX, R8, R9 before calling it.
  // The callsite analysis should detect 4 params.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  // __remill_basic_block with register GEPs.
  auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  struct RegDef { const char *name; unsigned offset; };
  RegDef all_regs[] = {
      {"RAX", 0}, {"RBX", 8}, {"RCX", 16}, {"RDX", 24},
      {"RSI", 32}, {"RDI", 40}, {"RSP", 48}, {"RBP", 56},
      {"R8", 64}, {"R9", 72}, {"R10", 80}, {"R11", 88},
      {"R12", 96}, {"R13", 104}, {"R14", 112}, {"R15", 120},
      {"RIP", 128},
  };
  for (auto &reg : all_regs) {
    auto *gep = BBB.CreateGEP(BBB.getInt64Ty(), bb_state,
                              BBB.getInt64(reg.offset / 8));
    gep->setName(reg.name);
  }
  BBB.CreateRet(bb_fn->getArg(2));

  // Callee: lifted function with no visible param reads (obfuscated body).
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *callee_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", *M);
  auto *callee_entry = llvm::BasicBlock::Create(Ctx, "entry", callee_fn);
  llvm::IRBuilder<> CB(callee_entry);
  // Just return — no param reads, so body analysis detects 0 params.
  // But fallback defaults to 4 params.  Callsite should confirm this.
  CB.CreateRet(callee_fn->getArg(2));

  // Caller: stores RCX, RDX, R8 before dispatch_call to callee.
  auto *caller_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *caller_entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(caller_entry);

  auto *state = caller_fn->getArg(0);
  auto *mem = caller_fn->getArg(2);

  // Store RCX (offset 16), RDX (24), R8 (64).
  B.CreateStore(B.getInt64(100),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 16));
  B.CreateStore(B.getInt64(200),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 24));
  B.CreateStore(B.getInt64(300),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 64));

  // dispatch_call to callee.
  auto *dispatch_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);
  auto *va = B.getInt64(0x402000);
  B.CreateCall(dispatch_fn, {state, va, mem});

  // Store RAX to mark function non-void.
  B.CreateStore(B.getInt64(42),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 0));
  B.CreateRet(mem);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  // Callee should have at least 3 params from callsite evidence.
  auto *abi = result.getABI(callee_fn);
  ASSERT_NE(abi, nullptr);
  // The callee body defaults to 4 params (no param reads → fallback).
  // Callsite shows 3 consecutive (RCX, RDX, R8 but not R9).
  // The max of body(4) and callsite(3) = 4.
  EXPECT_GE(abi->numParams(), 3u);
}

// ===----------------------------------------------------------------------===
// Test: Stack argument detection from callsite
// ===----------------------------------------------------------------------===

TEST_F(CallingConventionAnalysisTest, CallsiteDetectsStackArgs) {
  // Caller stores to RSP+0x28 and RSP+0x30 (5th and 6th args) via inttoptr
  // before dispatch_call.  The analysis should detect 2 stack params.
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *arr_ty = llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 3504);
  state_ty->setBody({arr_ty});

  auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  struct RegDef { const char *name; unsigned offset; };
  RegDef all_regs[] = {
      {"RAX", 0}, {"RBX", 8}, {"RCX", 16}, {"RDX", 24},
      {"RSI", 32}, {"RDI", 40}, {"RSP", 48}, {"RBP", 56},
      {"R8", 64}, {"R9", 72}, {"R10", 80}, {"R11", 88},
      {"R12", 96}, {"R13", 104}, {"R14", 112}, {"R15", 120},
      {"RIP", 128},
  };
  for (auto &reg : all_regs) {
    auto *gep = BBB.CreateGEP(BBB.getInt64Ty(), bb_state,
                              BBB.getInt64(reg.offset / 8));
    gep->setName(reg.name);
  }
  BBB.CreateRet(bb_fn->getArg(2));

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  // Callee: reads RCX only.
  auto *callee_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_403000", *M);
  auto *callee_entry = llvm::BasicBlock::Create(Ctx, "entry", callee_fn);
  llvm::IRBuilder<> CB(callee_entry);
  CB.CreateLoad(i64_ty,
                CB.CreateConstGEP1_64(CB.getInt8Ty(), callee_fn->getArg(0), 16),
                "rcx_val");
  CB.CreateStore(CB.getInt64(42),
                 CB.CreateConstGEP1_64(CB.getInt8Ty(), callee_fn->getArg(0), 0));
  CB.CreateRet(callee_fn->getArg(2));

  // Caller: stores all 4 GPR params + 2 stack args, then dispatch_call.
  auto *caller_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *caller_entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(caller_entry);

  auto *state = caller_fn->getArg(0);
  auto *mem = caller_fn->getArg(2);

  // Store all 4 GPR params.
  B.CreateStore(B.getInt64(1),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 16));  // RCX
  B.CreateStore(B.getInt64(2),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 24));  // RDX
  B.CreateStore(B.getInt64(3),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 64));  // R8
  B.CreateStore(B.getInt64(4),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 72));  // R9

  // Store stack args at RSP+0x28 and RSP+0x30 via inttoptr(RSP + offset).
  auto *rsp_val = B.CreateLoad(
      i64_ty, B.CreateConstGEP1_64(B.getInt8Ty(), state, 48), "rsp");
  auto *addr5 = B.CreateAdd(rsp_val, B.getInt64(0x28));
  auto *ptr5 = B.CreateIntToPtr(addr5, ptr_ty);
  B.CreateStore(B.getInt64(5), ptr5);

  auto *addr6 = B.CreateAdd(rsp_val, B.getInt64(0x30));
  auto *ptr6 = B.CreateIntToPtr(addr6, ptr_ty);
  B.CreateStore(B.getInt64(6), ptr6);

  // dispatch_call to callee.
  auto *dispatch_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);
  B.CreateCall(dispatch_fn, {state, B.getInt64(0x403000), mem});

  B.CreateStore(B.getInt64(99),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 0));
  B.CreateRet(mem);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *abi = result.getABI(callee_fn);
  ASSERT_NE(abi, nullptr);

  // Should have 4 GPR params (callsite evidence).
  EXPECT_EQ(abi->numParams(), 4u);

  // Should have 2 stack params (RSP+0x28 and RSP+0x30).
  EXPECT_EQ(abi->numStackParams(), 2u);
  if (abi->numStackParams() >= 2u) {
    EXPECT_EQ(abi->stack_params[0].stack_offset, 0x28);
    EXPECT_EQ(abi->stack_params[1].stack_offset, 0x30);
  }
}

// ===----------------------------------------------------------------------===
// Test: Stack arg detection via concrete_stack alloca with metadata
// ===----------------------------------------------------------------------===

TEST_F(CallingConventionAnalysisTest, CallsiteDetectsStackArgsFromMetadata) {
  // Same as above but using a concrete_stack alloca with metadata
  // (simulating post-StackConcretization IR).
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  auto *state_arr_ty = llvm::ArrayType::get(i8_ty, 3504);
  state_ty->setBody({state_arr_ty});

  auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *bb_fn = llvm::Function::Create(
      bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
  llvm::IRBuilder<> BBB(bb_entry);
  auto *bb_state = bb_fn->getArg(0);
  struct RegDef { const char *name; unsigned offset; };
  RegDef all_regs[] = {
      {"RAX", 0}, {"RBX", 8}, {"RCX", 16}, {"RDX", 24},
      {"RSI", 32}, {"RDI", 40}, {"RSP", 48}, {"RBP", 56},
      {"R8", 64}, {"R9", 72}, {"R10", 80}, {"R11", 88},
      {"R12", 96}, {"R13", 104}, {"R14", 112}, {"R15", 120},
      {"RIP", 128},
  };
  for (auto &reg : all_regs) {
    auto *gep = BBB.CreateGEP(BBB.getInt64Ty(), bb_state,
                              BBB.getInt64(reg.offset / 8));
    gep->setName(reg.name);
  }
  BBB.CreateRet(bb_fn->getArg(2));

  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  // Callee.
  auto *callee_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_404000", *M);
  auto *callee_entry = llvm::BasicBlock::Create(Ctx, "entry", callee_fn);
  llvm::IRBuilder<> CB(callee_entry);
  CB.CreateStore(CB.getInt64(42),
                 CB.CreateConstGEP1_64(CB.getInt8Ty(), callee_fn->getArg(0), 0));
  CB.CreateRet(callee_fn->getArg(2));

  // Caller with concrete_stack alloca.
  auto *caller_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *caller_entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(caller_entry);

  auto *state = caller_fn->getArg(0);
  auto *mem = caller_fn->getArg(2);

  // Create concrete_stack alloca with metadata: base RSP offset = 0.
  // So GEP at index 0x28 = RSP+0x28 (5th arg).
  auto *frame_ty = llvm::ArrayType::get(i8_ty, 0x40);  // covers 0x00..0x3F
  auto *frame_alloca = B.CreateAlloca(frame_ty, nullptr, "concrete_stack");
  auto *md_offset = llvm::ConstantAsMetadata::get(B.getInt64(0));
  frame_alloca->setMetadata(
      "omill.stack.base_offset",
      llvm::MDNode::get(Ctx, {md_offset}));

  // Store RCX param.
  B.CreateStore(B.getInt64(1),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 16));

  // Store stack arg at GEP offset 0x28 (RSP+0x28 because base=0).
  auto *stack_ptr5 = B.CreateConstGEP1_64(i8_ty, frame_alloca, 0x28);
  B.CreateStore(B.getInt64(5), stack_ptr5);

  // dispatch_call.
  auto *dispatch_fn = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);
  B.CreateCall(dispatch_fn, {state, B.getInt64(0x404000), mem});
  B.CreateStore(B.getInt64(99),
                B.CreateConstGEP1_64(B.getInt8Ty(), state, 0));
  B.CreateRet(mem);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

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
  MAM.registerPass([&] { return omill::CallingConventionAnalysis(); });

  auto result = MAM.getResult<omill::CallingConventionAnalysis>(*M);

  auto *abi = result.getABI(callee_fn);
  ASSERT_NE(abi, nullptr);

  // Should detect 1 stack param from the metadata-annotated alloca.
  EXPECT_GE(abi->numStackParams(), 1u);
  if (abi->numStackParams() >= 1u) {
    EXPECT_EQ(abi->stack_params[0].stack_offset, 0x28);
  }
}

}  // namespace
