#include "omill/Passes/VMDispatchResolution.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VMHandlerGraph.h"

#include <gtest/gtest.h>

#include <memory>
#include <vector>

namespace {

class VMDispatchResolutionTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  omill::BinaryMemoryMap MemMap;
  std::vector<std::unique_ptr<uint8_t[]>> Buffers;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    return M;
  }

  llvm::FunctionType *liftedFnType() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  llvm::Function *declareDispatchJump(llvm::Module &M) {
    auto *existing = M.getFunction("__omill_dispatch_jump");
    if (existing)
      return existing;
    return llvm::Function::Create(liftedFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  "__omill_dispatch_jump", M);
  }

  llvm::Function *declareOpaqueBase(llvm::Module &M) {
    auto *existing = M.getFunction("opaque_base");
    if (existing)
      return existing;
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(i64_ty, {}, false);
    return llvm::Function::Create(ft, llvm::GlobalValue::ExternalLinkage,
                                  "opaque_base", M);
  }

  llvm::Function *createHandler(llvm::Module &M, llvm::StringRef name) {
    auto *F = llvm::Function::Create(liftedFnType(),
                                     llvm::GlobalValue::ExternalLinkage, name,
                                     M);
    F->addFnAttr("omill.vm_handler");
    return F;
  }

  llvm::CallInst *findDispatchJump(llvm::Function *F) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (callee && callee->getName() == "__omill_dispatch_jump")
          return call;
      }
    }
    return nullptr;
  }

  void addI32(uint64_t addr, uint32_t value) {
    auto buffer = std::make_unique<uint8_t[]>(4);
    for (unsigned i = 0; i < 4; ++i)
      buffer[i] = static_cast<uint8_t>((value >> (i * 8)) & 0xFF);
    auto *data = buffer.get();
    Buffers.push_back(std::move(buffer));
    MemMap.addRegion(addr, data, 4);
  }

  void runPass(llvm::Module &M, omill::VMHandlerGraph graph = {}) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass([&] { return omill::BinaryMemoryAnalysis(MemMap); });
    MAM.registerPass(
        [&] { return omill::VMHandlerGraphAnalysis(std::move(graph)); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    (void)MAM.getResult<omill::BinaryMemoryAnalysis>(M);
    (void)MAM.getResult<omill::VMHandlerGraphAnalysis>(M);

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::VMDispatchResolutionPass());
    MPM.run(M, MAM);
  }
};

TEST_F(VMDispatchResolutionTest, ResolvesLoadBackedRVAWithoutGraph) {
  auto M = createModule();
  MemMap.setImageBase(0x100000000ULL);
  addI32(0x100004000ULL, 0x2500);

  auto *handler = createHandler(*M, "sub_100001000");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *rva_ptr = B.CreateIntToPtr(B.getInt64(0x100004000ULL),
                                   llvm::PointerType::get(Ctx, 0));
  auto *rva = B.CreateLoad(llvm::Type::getInt32Ty(Ctx), rva_ptr);
  auto *target = B.CreateAdd(opaque_base, B.CreateZExt(rva, B.getInt64Ty()));
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100002500ULL);

  auto *md = M->getNamedMetadata("omill.vm_discovered_targets");
  ASSERT_NE(md, nullptr);
  ASSERT_EQ(md->getNumOperands(), 1u);
}

TEST_F(VMDispatchResolutionTest, ResolvesSelectWithKnownCondition) {
  auto M = createModule();
  MemMap.setImageBase(0x100000000ULL);
  addI32(0x100004100ULL, 1);

  auto *handler = createHandler(*M, "sub_100001080");
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", handler);
  llvm::IRBuilder<> B(entry);

  auto *dispatch = declareDispatchJump(*M);
  auto *opaque_base = B.CreateCall(declareOpaqueBase(*M));
  auto *cond_ptr = B.CreateIntToPtr(B.getInt64(0x100004100ULL),
                                    llvm::PointerType::get(Ctx, 0));
  auto *cond_word = B.CreateLoad(llvm::Type::getInt32Ty(Ctx), cond_ptr);
  auto *cond = B.CreateICmpEQ(cond_word, B.getInt32(1));
  auto *rva = B.CreateSelect(cond, B.getInt64(0x1200), B.getInt64(0x1300));
  auto *target = B.CreateAdd(opaque_base, rva);
  auto *jump = B.CreateCall(dispatch,
                            {handler->getArg(0), target, handler->getArg(2)});
  B.CreateRet(jump);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  auto *resolved = llvm::dyn_cast<llvm::ConstantInt>(jump->getArgOperand(1));
  ASSERT_NE(resolved, nullptr);
  EXPECT_EQ(resolved->getZExtValue(), 0x100001200ULL);
}

}  // namespace
