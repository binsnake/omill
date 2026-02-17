#include "omill/Passes/InterProceduralConstProp.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>

namespace {

class InterProceduralConstPropTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  // Use simplified offsets for testing: RCX=16, RDX=24, R8=64, R9=72
  // matching the test State layout used in CallingConventionAnalysisTest.
  static constexpr unsigned kRCX = 16;
  static constexpr unsigned kRDX = 24;

  llvm::FunctionType *liftedFnTy() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
        "n8:16:32:64-S128");

    // Create __remill_basic_block with register GEPs for StateFieldMap.
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *bb_fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);
    auto *bb_state = bb_fn->getArg(0);

    struct RegDef { const char *name; unsigned offset; };
    RegDef regs[] = {
        {"RAX", 0}, {"RBX", 8}, {"RCX", 16}, {"RDX", 24},
        {"RSI", 32}, {"RDI", 40}, {"RSP", 48}, {"RBP", 56},
        {"R8", 64}, {"R9", 72},
    };
    for (auto &reg : regs) {
      BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, reg.offset, reg.name);
    }
    BBB.CreateRet(bb_fn->getArg(2));

    return M;
  }

  /// Create a callee that loads from State+offset in entry block.
  llvm::Function *createCallee(llvm::Module &M, const char *name,
                                unsigned load_offset) {
    auto *fn = llvm::Function::Create(
        liftedFnTy(), llvm::Function::ExternalLinkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(entry);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), fn->getArg(0), load_offset);
    auto *val = B.CreateLoad(B.getInt64Ty(), gep, "param_val");
    // Use the loaded value somehow (store back to RAX).
    auto *rax_gep = B.CreateConstGEP1_64(B.getInt8Ty(), fn->getArg(0), 0);
    B.CreateStore(val, rax_gep);
    B.CreateRet(fn->getArg(2));
    return fn;
  }

  /// Create a caller that stores a constant to State+offset then calls callee.
  llvm::Function *createCaller(llvm::Module &M, const char *name,
                                llvm::Function *callee,
                                unsigned store_offset, uint64_t const_val) {
    auto *fn = llvm::Function::Create(
        liftedFnTy(), llvm::Function::ExternalLinkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(entry);
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), fn->getArg(0), store_offset);
    B.CreateStore(B.getInt64(const_val), gep);
    auto *result = B.CreateCall(callee,
        {fn->getArg(0), fn->getArg(1), fn->getArg(2)});
    B.CreateRet(result);
    return fn;
  }

  llvm::PreservedAnalyses runPass(llvm::Module &M) {
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
    MAM.registerPass([&] { return omill::LiftedFunctionAnalysis(); });
    MAM.registerPass([&] { return omill::CallGraphAnalysis(); });

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::InterProceduralConstPropPass());
    return MPM.run(M, MAM);
  }
};

TEST_F(InterProceduralConstPropTest, SingleCallerConstRCX) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_402000", kRCX);
  createCaller(*M, "sub_401000", callee, kRCX, 42);

  runPass(*M);

  // The load in callee's entry block should be replaced with 42.
  auto *entry = &callee->getEntryBlock();
  bool found_const = false;
  for (auto &I : *entry) {
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand())) {
        if (C->getZExtValue() == 42) {
          found_const = true;
        }
      }
    }
  }
  EXPECT_TRUE(found_const);
}

TEST_F(InterProceduralConstPropTest, TwoCallersSameConst) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_403000", kRCX);
  createCaller(*M, "sub_401000", callee, kRCX, 100);
  createCaller(*M, "sub_402000", callee, kRCX, 100);

  runPass(*M);

  // Both callers store 100 → should be propagated.
  bool found_const = false;
  for (auto &I : callee->getEntryBlock()) {
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand())) {
        if (C->getZExtValue() == 100) {
          found_const = true;
        }
      }
    }
  }
  EXPECT_TRUE(found_const);
}

TEST_F(InterProceduralConstPropTest, TwoCallersDifferentConsts) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_403000", kRCX);
  createCaller(*M, "sub_401000", callee, kRCX, 42);
  createCaller(*M, "sub_402000", callee, kRCX, 99);

  runPass(*M);

  // Different constants → should NOT be propagated. Load should remain.
  bool has_load = false;
  for (auto &I : callee->getEntryBlock()) {
    if (llvm::isa<llvm::LoadInst>(&I)) {
      has_load = true;
    }
  }
  EXPECT_TRUE(has_load);
}

TEST_F(InterProceduralConstPropTest, EntryPointUnchanged) {
  auto M = createModule();
  // Callee with no callers (entry point).
  auto *callee = createCallee(*M, "sub_401000", kRCX);

  runPass(*M);

  // No callers → should not be modified.
  bool has_load = false;
  for (auto &I : callee->getEntryBlock()) {
    if (llvm::isa<llvm::LoadInst>(&I)) {
      has_load = true;
    }
  }
  EXPECT_TRUE(has_load);
}

TEST_F(InterProceduralConstPropTest, NonConstantStoreBlocks) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_402000", kRCX);

  // Caller stores a non-constant (loaded from State) to RCX.
  auto *caller_fn = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_fn);
  llvm::IRBuilder<> B(entry);
  // Load some dynamic value.
  auto *dynamic = B.CreateLoad(B.getInt64Ty(), caller_fn->getArg(0));
  auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), caller_fn->getArg(0), kRCX);
  B.CreateStore(dynamic, gep);
  auto *result = B.CreateCall(callee,
      {caller_fn->getArg(0), caller_fn->getArg(1), caller_fn->getArg(2)});
  B.CreateRet(result);

  runPass(*M);

  // Non-constant store → load should remain.
  bool has_load = false;
  for (auto &I : callee->getEntryBlock()) {
    if (llvm::isa<llvm::LoadInst>(&I)) {
      has_load = true;
    }
  }
  EXPECT_TRUE(has_load);
}

TEST_F(InterProceduralConstPropTest, AddressTakenFunctionSkipped) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_402000", kRCX);
  createCaller(*M, "sub_401000", callee, kRCX, 42);

  // Take the address of the callee (ptrtoint) — this should prevent propagation.
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *addr_fn = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {}, false),
      llvm::Function::ExternalLinkage, "get_addr", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", addr_fn);
  llvm::IRBuilder<> B(entry);
  auto *addr = B.CreatePtrToInt(callee, i64_ty);
  B.CreateRet(addr);

  runPass(*M);

  // With address taken, the callee's load should remain (conservative).
  bool has_load = false;
  for (auto &I : callee->getEntryBlock()) {
    if (llvm::isa<llvm::LoadInst>(&I))
      has_load = true;
  }
  EXPECT_TRUE(has_load);
}

TEST_F(InterProceduralConstPropTest, MultipleCallersAgree) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_403000", kRCX);
  createCaller(*M, "sub_401000", callee, kRCX, 100);
  createCaller(*M, "sub_402000", callee, kRCX, 100);

  runPass(*M);

  // Both callers store 100 → propagation should happen.
  bool found_const = false;
  for (auto &I : callee->getEntryBlock()) {
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand())) {
        if (C->getZExtValue() == 100)
          found_const = true;
      }
    }
  }
  EXPECT_TRUE(found_const);
}

TEST_F(InterProceduralConstPropTest, MultipleCallersDisagree) {
  auto M = createModule();
  auto *callee = createCallee(*M, "sub_403000", kRCX);
  createCaller(*M, "sub_401000", callee, kRCX, 42);
  createCaller(*M, "sub_402000", callee, kRCX, 99);

  runPass(*M);

  // Different constants → no propagation, load should remain.
  bool has_load = false;
  for (auto &I : callee->getEntryBlock()) {
    if (llvm::isa<llvm::LoadInst>(&I))
      has_load = true;
  }
  EXPECT_TRUE(has_load);
}

}  // namespace
