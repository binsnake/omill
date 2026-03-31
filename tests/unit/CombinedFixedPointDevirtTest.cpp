#include "omill/Passes/CombinedFixedPointDevirt.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class CombinedFixedPointDevirtTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  void runPass(llvm::Module &M, omill::BinaryMemoryMap map) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass(
        [&] { return omill::BinaryMemoryAnalysis(std::move(map)); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    llvm::ModulePassManager MPM;
    MPM.addPass(
        llvm::RequireAnalysisPass<omill::BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::CombinedFixedPointDevirtPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    MPM.run(M, MAM);
  }

  llvm::Function *declareRemillRead64(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
    return llvm::cast<llvm::Function>(
        M.getOrInsertFunction("__remill_read_memory_64", fn_ty).getCallee());
  }
};

TEST_F(CombinedFixedPointDevirtTest,
       ConcretizedBinaryLoadParticipatesInSameRoundConstantPropagation) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *addrConst = llvm::ConstantInt::get(i64Ty, 0x1000);
  auto *ptr = llvm::ConstantExpr::getIntToPtr(addrConst, ptrTy);
  auto *load = B.CreateLoad(i64Ty, ptr);
  auto *xored = B.CreateXor(load, llvm::ConstantInt::get(i64Ty, 0x10));
  auto *added = B.CreateAdd(xored, llvm::ConstantInt::get(i64Ty, 1));
  B.CreateRet(added);

  uint8_t data[8] = {0x78, 0x56, 0x34, 0x12, 0, 0, 0, 0};
  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, sizeof(data), /*read_only=*/true);

  runPass(*M, std::move(map));

  auto *ret = llvm::cast<llvm::ReturnInst>(entry->getTerminator());
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
  ASSERT_NE(ci, nullptr);
  EXPECT_EQ(ci->getZExtValue(), (0x12345678ULL ^ 0x10ULL) + 1ULL);
}

TEST_F(CombinedFixedPointDevirtTest,
       SameBlockStoreToLoadForwardingFeedsLaterSimplification) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto *slot = B.CreateAlloca(i64Ty, nullptr, "slot");
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x4000), slot);
  auto *value = B.CreateLoad(i64Ty, slot);
  auto *sum = B.CreateAdd(value, llvm::ConstantInt::get(i64Ty, 0x20));
  B.CreateRet(sum);

  omill::BinaryMemoryMap map;
  runPass(*M, std::move(map));

  auto *ret = llvm::cast<llvm::ReturnInst>(entry->getTerminator());
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
  ASSERT_NE(ci, nullptr);
  EXPECT_EQ(ci->getZExtValue(), 0x4020ULL);
}

TEST_F(CombinedFixedPointDevirtTest,
       StackLikeIntToPtrStoreLoadForwardingFeedsLaterSimplification) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i64Ty, ptrTy}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto args = fn->args().begin();
  llvm::Value *stackBase = &*args++;
  llvm::Value *state = &*args++;

  auto *pcSlotAddr = B.CreateAdd(stackBase, llvm::ConstantInt::get(i64Ty, -24));
  auto *pcSlot = B.CreateIntToPtr(pcSlotAddr, ptrTy);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x18005C2F4ULL), pcSlot);

  auto *scratchAddr = B.CreateAdd(stackBase, llvm::ConstantInt::get(i64Ty, -8));
  auto *scratchSlot = B.CreateIntToPtr(scratchAddr, ptrTy);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 1), scratchSlot);

  auto *stateField =
      B.CreateConstGEP1_64(llvm::Type::getInt8Ty(Ctx), state, 16);
  B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt8Ty(Ctx), 7),
                stateField);

  auto *loadedPc = B.CreateLoad(i64Ty, pcSlot);
  auto *jumpTarget =
      B.CreateAdd(loadedPc, llvm::ConstantInt::get(i64Ty, 22298));
  B.CreateRet(jumpTarget);

  omill::BinaryMemoryMap map;
  runPass(*M, std::move(map));

  auto *ret = llvm::cast<llvm::ReturnInst>(entry->getTerminator());
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
  ASSERT_NE(ci, nullptr);
  EXPECT_EQ(ci->getZExtValue(), 0x180061A0EULL);
}

TEST_F(CombinedFixedPointDevirtTest,
       VmHelperStyleStackStoreLoadForwardingFeedsRemillJumpTarget) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *fnTy = llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "blk_18006542b", *M);
  auto *jump = llvm::Function::Create(
      fnTy, llvm::GlobalValue::ExternalLinkage, "__remill_jump", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto args = fn->args().begin();
  llvm::Value *state = &*args++;
  llvm::Value *programCounter = &*args++;
  llvm::Value *memory = &*args++;
  auto *i8Ty = llvm::Type::getInt8Ty(Ctx);

  auto *rbpPtr = B.CreateConstGEP1_64(i8Ty, state, 2328);
  auto *rspPtr = B.CreateConstGEP1_64(i8Ty, state, 2312);
  auto *pcPtr = B.CreateConstGEP1_64(i8Ty, state, 2472);
  auto *r11Ptr = B.CreateConstGEP1_64(i8Ty, state, 2392);
  auto *rdiPtr = B.CreateConstGEP1_64(i8Ty, state, 2296);

  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x100000), rspPtr);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x2222), rbpPtr);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x3333), r11Ptr);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x4444), rdiPtr);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0), pcPtr);

  auto *sp = B.CreateLoad(i64Ty, rspPtr);
  auto *spPlus8 = B.CreateAdd(sp, llvm::ConstantInt::get(i64Ty, 8));
  auto *rbp = B.CreateLoad(i64Ty, rbpPtr);
  auto *slot0 = B.CreateIntToPtr(spPlus8, ptrTy);
  B.CreateStore(rbp, slot0);

  auto *pcSaveAddr = B.CreateAdd(sp, llvm::ConstantInt::get(i64Ty, -8));
  auto *pcSaveSlot = B.CreateIntToPtr(pcSaveAddr, ptrTy);
  auto *nextPc = B.CreateAdd(programCounter, llvm::ConstantInt::get(i64Ty, 10));
  B.CreateStore(nextPc, pcSaveSlot);

  auto *slotNeg16Addr = B.CreateAdd(sp, llvm::ConstantInt::get(i64Ty, -16));
  auto *slotNeg16 = B.CreateIntToPtr(slotNeg16Addr, ptrTy);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x180028034ULL), slotNeg16);

  auto *r11 = B.CreateLoad(i64Ty, r11Ptr);
  auto *slotSp = B.CreateIntToPtr(sp, ptrTy);
  B.CreateStore(r11, slotSp);
  auto *tmp16 = B.CreateLoad(i64Ty, slotNeg16);
  B.CreateStore(tmp16, r11Ptr);
  B.CreateStore(llvm::ConstantInt::get(i32Ty, static_cast<uint32_t>(-1399144419)),
                slotNeg16);

  auto *slotNeg24Addr = B.CreateAdd(sp, llvm::ConstantInt::get(i64Ty, -24));
  auto *slotNeg24 = B.CreateIntToPtr(slotNeg24Addr, ptrTy);
  B.CreateStore(llvm::ConstantInt::get(i64Ty, 0x18005C2F4ULL), slotNeg24);

  auto *rdi = B.CreateLoad(i64Ty, rdiPtr);
  B.CreateStore(rdi, pcSaveSlot);
  B.CreateStore(slotNeg16Addr, rspPtr);

  auto *loadedTargetBase = B.CreateLoad(i64Ty, slotNeg24);
  auto *jumpTarget =
      B.CreateAdd(loadedTargetBase, llvm::ConstantInt::get(i64Ty, 22298));
  B.CreateStore(jumpTarget, rdiPtr);
  B.CreateStore(jumpTarget, pcPtr);
  auto *jumpCall = B.CreateCall(jump, {state, jumpTarget, memory});
  B.CreateRet(jumpCall);

  omill::BinaryMemoryMap map;
  runPass(*M, std::move(map));

  auto *ret = llvm::cast<llvm::ReturnInst>(entry->getTerminator());
  auto *call = llvm::dyn_cast<llvm::CallInst>(ret->getReturnValue());
  ASSERT_NE(call, nullptr);
  auto *targetCi = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
  ASSERT_NE(targetCi, nullptr);
  EXPECT_EQ(targetCi->getZExtValue(), 0x180061A0EULL);
}

TEST_F(CombinedFixedPointDevirtTest,
       SelectOfTwoConstantAddressesBecomesSelectOfConstants) {
  auto M = createModule();
  auto *i1Ty = llvm::Type::getInt1Ty(Ctx);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i1Ty}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto *cond = fn->getArg(0);
  auto *ptr1 = llvm::ConstantExpr::getIntToPtr(
      llvm::ConstantInt::get(i64Ty, 0x2000), llvm::PointerType::get(Ctx, 0));
  auto *ptr2 = llvm::ConstantExpr::getIntToPtr(
      llvm::ConstantInt::get(i64Ty, 0x2008), llvm::PointerType::get(Ctx, 0));
  auto *ptr = B.CreateSelect(cond, ptr1, ptr2, "ptr");
  auto *value = B.CreateLoad(i64Ty, ptr);
  B.CreateRet(value);

  uint8_t data[16] = {0x11, 0, 0, 0, 0, 0, 0, 0,
                      0x22, 0, 0, 0, 0, 0, 0, 0};
  omill::BinaryMemoryMap map;
  map.addRegion(0x2000, data, sizeof(data), /*read_only=*/true);

  runPass(*M, std::move(map));

  auto *ret = llvm::cast<llvm::ReturnInst>(entry->getTerminator());
  EXPECT_FALSE(llvm::isa<llvm::LoadInst>(ret->getReturnValue()));
  unsigned load_count = 0;
  for (auto &BB : *fn)
    for (auto &I : BB)
      if (llvm::isa<llvm::LoadInst>(&I))
        ++load_count;
  EXPECT_EQ(load_count, 0u);
}

TEST_F(CombinedFixedPointDevirtTest,
       SelectOfTwoConstantRemillReadsBecomesSelectOfConstants) {
  auto M = createModule();
  auto *i1Ty = llvm::Type::getInt1Ty(Ctx);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);
  auto *readMem = declareRemillRead64(*M);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {i1Ty}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  auto *cond = fn->getArg(0);
  auto *addr =
      B.CreateSelect(cond, llvm::ConstantInt::get(i64Ty, 0x3000),
                     llvm::ConstantInt::get(i64Ty, 0x3008), "addr");
  auto *value =
      B.CreateCall(readMem, {llvm::ConstantPointerNull::get(ptrTy), addr});
  B.CreateRet(value);

  uint8_t data[16] = {0x33, 0, 0, 0, 0, 0, 0, 0,
                      0x44, 0, 0, 0, 0, 0, 0, 0};
  omill::BinaryMemoryMap map;
  map.addRegion(0x3000, data, sizeof(data), /*read_only=*/true);

  runPass(*M, std::move(map));

  auto *ret = llvm::cast<llvm::ReturnInst>(entry->getTerminator());
  auto *sel = llvm::dyn_cast<llvm::SelectInst>(ret->getReturnValue());
  ASSERT_NE(sel, nullptr);
  auto *true_ci = llvm::dyn_cast<llvm::ConstantInt>(sel->getTrueValue());
  auto *false_ci = llvm::dyn_cast<llvm::ConstantInt>(sel->getFalseValue());
  ASSERT_NE(true_ci, nullptr);
  ASSERT_NE(false_ci, nullptr);
  EXPECT_EQ(true_ci->getZExtValue(), 0x33ULL);
  EXPECT_EQ(false_ci->getZExtValue(), 0x44ULL);
}

}  // namespace
