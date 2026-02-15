#include "omill/Passes/ConstantMemoryFolding.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"

#include <cstring>
#include <gtest/gtest.h>

namespace {

class ConstantMemoryFoldingTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    return M;
  }

  /// Create a function with a single load from inttoptr(addr).
  llvm::Function *createLoadFunction(llvm::Module &M, llvm::StringRef name,
                                     llvm::Type *load_ty, uint64_t addr) {
    auto *fn_ty =
        llvm::FunctionType::get(load_ty, {}, false);
    auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                      name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(entry);

    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *addr_const = llvm::ConstantInt::get(i64_ty, addr);
    auto *ptr = llvm::ConstantExpr::getIntToPtr(addr_const, ptr_ty);
    auto *load = B.CreateLoad(load_ty, ptr);
    B.CreateRet(load);
    return fn;
  }

  /// Run the pass with the given memory map.
  void runPass(llvm::Module &M, omill::BinaryMemoryMap map) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    // Register our analysis BEFORE standard analyses so it doesn't get
    // overwritten.
    MAM.registerPass(
        [&] { return omill::BinaryMemoryAnalysis(std::move(map)); });

    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    llvm::ModulePassManager MPM;
    // Ensure the module analysis is cached before function passes.
    MPM.addPass(
        llvm::RequireAnalysisPass<omill::BinaryMemoryAnalysis, llvm::Module>());
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::ConstantMemoryFoldingPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    MPM.run(M, MAM);
  }
};

TEST_F(ConstantMemoryFoldingTest, LoadFromConstantAddressFolded) {
  auto M = createModule();
  createLoadFunction(*M, "test_fn", llvm::Type::getInt64Ty(Ctx), 0x1000);

  // Set up memory: 8 bytes at address 0x1000 = 0xDEADBEEF12345678
  uint8_t data[8] = {0x78, 0x56, 0x34, 0x12, 0xEF, 0xBE, 0xAD, 0xDE};
  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 8);

  runPass(*M, std::move(map));

  auto *fn = M->getFunction("test_fn");
  ASSERT_NE(fn, nullptr);

  // The return instruction should now return a constant.
  auto &entry = fn->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(entry.getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
  ASSERT_NE(ci, nullptr);
  EXPECT_EQ(ci->getZExtValue(), 0xDEADBEEF12345678ULL);
}

TEST_F(ConstantMemoryFoldingTest, LoadFromUnmappedAddressUnchanged) {
  auto M = createModule();
  createLoadFunction(*M, "test_fn", llvm::Type::getInt64Ty(Ctx), 0x2000);

  // Map only 0x1000-0x1008, load is at 0x2000 = unmapped.
  uint8_t data[8] = {0};
  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 8);

  runPass(*M, std::move(map));

  auto *fn = M->getFunction("test_fn");
  auto &entry = fn->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(entry.getTerminator());
  ASSERT_NE(ret, nullptr);
  // Should still be a load, not a constant.
  EXPECT_TRUE(llvm::isa<llvm::LoadInst>(ret->getReturnValue()));
}

TEST_F(ConstantMemoryFoldingTest, GEPChainResolved) {
  auto M = createModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, {}, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  // gep(inttoptr(0x1000), i32 2) with i32 element type => offset = 8 bytes
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *addr_const = llvm::ConstantInt::get(i64_ty, 0x1000);
  auto *base_ptr = llvm::ConstantExpr::getIntToPtr(addr_const, ptr_ty);
  auto *gep =
      B.CreateGEP(i32_ty, base_ptr, llvm::ConstantInt::get(i32_ty, 2));
  auto *load = B.CreateLoad(i32_ty, gep);
  B.CreateRet(load);

  // Map 16 bytes at 0x1000. Value at offset 8 = 0x42424242.
  uint8_t data[16] = {};
  data[8] = 0x42;
  data[9] = 0x42;
  data[10] = 0x42;
  data[11] = 0x42;

  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 16);

  runPass(*M, std::move(map));

  auto &blk = fn->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(blk.getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
  ASSERT_NE(ci, nullptr);
  EXPECT_EQ(ci->getZExtValue(), 0x42424242u);
}

TEST_F(ConstantMemoryFoldingTest, MultipleTypesFolded) {
  auto M = createModule();

  // Set up memory: bytes 0x1000..0x100F with incrementing pattern.
  uint8_t data[16] = {0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88,
                      0x99, 0xAA, 0xBB, 0xCC, 0xDD, 0xEE, 0xFF, 0x00};

  // i8 at 0x1000
  createLoadFunction(*M, "load_i8", llvm::Type::getInt8Ty(Ctx), 0x1000);
  // i16 at 0x1002
  createLoadFunction(*M, "load_i16", llvm::Type::getInt16Ty(Ctx), 0x1002);
  // i32 at 0x1004
  createLoadFunction(*M, "load_i32", llvm::Type::getInt32Ty(Ctx), 0x1004);

  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 16);

  runPass(*M, std::move(map));

  // Check i8
  {
    auto *fn = M->getFunction("load_i8");
    auto *ret =
        llvm::dyn_cast<llvm::ReturnInst>(fn->getEntryBlock().getTerminator());
    auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
    ASSERT_NE(ci, nullptr);
    EXPECT_EQ(ci->getZExtValue(), 0x11u);
  }

  // Check i16 at offset 2 = bytes 0x33, 0x44 => LE = 0x4433
  {
    auto *fn = M->getFunction("load_i16");
    auto *ret =
        llvm::dyn_cast<llvm::ReturnInst>(fn->getEntryBlock().getTerminator());
    auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
    ASSERT_NE(ci, nullptr);
    EXPECT_EQ(ci->getZExtValue(), 0x4433u);
  }

  // Check i32 at offset 4 = bytes 0x55, 0x66, 0x77, 0x88 => LE = 0x88776655
  {
    auto *fn = M->getFunction("load_i32");
    auto *ret =
        llvm::dyn_cast<llvm::ReturnInst>(fn->getEntryBlock().getTerminator());
    auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
    ASSERT_NE(ci, nullptr);
    EXPECT_EQ(ci->getZExtValue(), 0x88776655u);
  }
}

TEST_F(ConstantMemoryFoldingTest, FloatLoadFolded) {
  auto M = createModule();
  createLoadFunction(*M, "test_fn", llvm::Type::getFloatTy(Ctx), 0x1000);

  // float 3.14f = 0x4048F5C3 in IEEE754
  uint32_t float_bits = 0x4048F5C3u;
  uint8_t data[4];
  std::memcpy(data, &float_bits, 4);
  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 4);

  runPass(*M, std::move(map));

  auto *fn = M->getFunction("test_fn");
  auto &entry = fn->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(entry.getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *cfp = llvm::dyn_cast<llvm::ConstantFP>(ret->getReturnValue());
  ASSERT_NE(cfp, nullptr);
  float result = cfp->getValueAPF().convertToFloat();
  EXPECT_NEAR(result, 3.14f, 1e-5f);
}

TEST_F(ConstantMemoryFoldingTest, DoubleLoadFolded) {
  auto M = createModule();
  createLoadFunction(*M, "test_fn", llvm::Type::getDoubleTy(Ctx), 0x1000);

  // double 2.718281828 in IEEE754
  double dval = 2.718281828;
  uint8_t data[8];
  std::memcpy(data, &dval, 8);
  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 8);

  runPass(*M, std::move(map));

  auto *fn = M->getFunction("test_fn");
  auto &entry = fn->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(entry.getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *cfp = llvm::dyn_cast<llvm::ConstantFP>(ret->getReturnValue());
  ASSERT_NE(cfp, nullptr);
  double result = cfp->getValueAPF().convertToDouble();
  EXPECT_NEAR(result, 2.718281828, 1e-9);
}

TEST_F(ConstantMemoryFoldingTest, ChainedGEPResolved) {
  auto M = createModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(i32_ty, {}, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);

  // gep(gep(inttoptr(0x1000), i32 2), i32 1) with i32 element type
  // => offset = (2+1) * 4 = 12 bytes
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *addr_const = llvm::ConstantInt::get(i64_ty, 0x1000);
  auto *base_ptr = llvm::ConstantExpr::getIntToPtr(addr_const, ptr_ty);
  auto *gep1 =
      llvm::ConstantExpr::getGetElementPtr(i32_ty, base_ptr,
                                            llvm::ConstantInt::get(i32_ty, 2));
  auto *gep2 = B.CreateGEP(i32_ty, gep1, llvm::ConstantInt::get(i32_ty, 1));
  auto *load = B.CreateLoad(i32_ty, gep2);
  B.CreateRet(load);

  // Map 16 bytes at 0x1000. Value at offset 12 = 0xCAFEBABE.
  uint8_t data[16] = {};
  data[12] = 0xBE;
  data[13] = 0xBA;
  data[14] = 0xFE;
  data[15] = 0xCA;

  omill::BinaryMemoryMap map;
  map.addRegion(0x1000, data, 16);

  runPass(*M, std::move(map));

  auto &blk = fn->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(blk.getTerminator());
  ASSERT_NE(ret, nullptr);
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ret->getReturnValue());
  ASSERT_NE(ci, nullptr);
  EXPECT_EQ(ci->getZExtValue(), 0xCAFEBABEu);
}

}  // namespace
