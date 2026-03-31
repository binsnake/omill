#include "omill/Passes/JumpTableConcretizer.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Omill.h"

#include <gtest/gtest.h>

namespace {

static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class JumpTableConcretizerTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  omill::BinaryMemoryMap mem_map;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  void runPass(llvm::Function *F) {
    auto *M = F->getParent();

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

    // Register BinaryMemoryAnalysis with our test map.
    MAM.registerPass([this] {
      return omill::BinaryMemoryAnalysis(mem_map);
    });
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });

    // Pre-cache the analyses.
    (void)MAM.getResult<omill::BinaryMemoryAnalysis>(*M);
    (void)MAM.getResult<omill::LiftedFunctionAnalysis>(*M);

    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::JumpTableConcretizerPass());
    FPM.run(*F, FAM);
  }

  /// The standard lifted function type: (State*, i64, Memory*) -> Memory*
  llvm::FunctionType *getLiftedFnType() {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);
    return llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
  }

  /// Create __omill_dispatch_jump declaration.
  llvm::Function *declareDispatch(llvm::Module &M) {
    auto *fn = M.getFunction("__omill_dispatch_jump");
    if (fn)
      return fn;
    return llvm::Function::Create(getLiftedFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  "__omill_dispatch_jump", &M);
  }

  /// Create a lifted function with a jump table dispatch pattern.
  /// Pattern:
  ///   entry:
  ///     %cmp = icmp ult %idx, <num_entries>
  ///     br %cmp, %jt_bb, %default_bb
  ///   jt_bb:
  ///     %addr = add(shl(%idx, 3), table_base)
  ///     %ptr = inttoptr %addr
  ///     %target = load i64, ptr %ptr
  ///     %r = call @__omill_dispatch_jump(state, %target, mem)
  ///     ret %r
  ///   default_bb:
  ///     %r2 = call @__omill_dispatch_jump(state, 0, mem)
  ///     ret %r2
  llvm::Function *createJumpTableFunction(
      llvm::Module &M, const char *name, uint64_t table_base,
      unsigned stride, unsigned num_entries) {
    auto *fn = llvm::Function::Create(getLiftedFnType(),
                                      llvm::GlobalValue::ExternalLinkage,
                                      name, &M);
    auto *dispatch = declareDispatch(M);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    auto *jt_bb = llvm::BasicBlock::Create(Ctx, "jt_bb", fn);
    auto *def_bb = llvm::BasicBlock::Create(Ctx, "default_bb", fn);

    // Index is the second argument (pc).
    auto *idx = fn->getArg(1);

    // entry: bounds check
    llvm::IRBuilder<> B(entry);
    auto *cmp = B.CreateICmpULT(idx,
        llvm::ConstantInt::get(i64Ty, num_entries));
    B.CreateCondBr(cmp, jt_bb, def_bb);

    // jt_bb: table load + dispatch
    B.SetInsertPoint(jt_bb);
    llvm::Value *addr;
    if (stride == 8) {
      auto *shifted = B.CreateShl(idx, llvm::ConstantInt::get(i64Ty, 3));
      addr = B.CreateAdd(shifted,
                         llvm::ConstantInt::get(i64Ty, table_base));
    } else if (stride == 4) {
      auto *shifted = B.CreateShl(idx, llvm::ConstantInt::get(i64Ty, 2));
      addr = B.CreateAdd(shifted,
                         llvm::ConstantInt::get(i64Ty, table_base));
    } else {
      auto *scaled = B.CreateMul(idx,
          llvm::ConstantInt::get(i64Ty, stride));
      addr = B.CreateAdd(scaled,
                         llvm::ConstantInt::get(i64Ty, table_base));
    }
    auto *ptr = B.CreateIntToPtr(addr, ptrTy);

    llvm::Type *load_ty = (stride == 4) ? llvm::Type::getInt32Ty(Ctx) : i64Ty;
    auto *target_raw = B.CreateLoad(load_ty, ptr);
    llvm::Value *target = target_raw;
    if (stride == 4) {
      target = B.CreateSExt(target_raw, i64Ty);
      target = B.CreateAdd(target,
          llvm::ConstantInt::get(i64Ty, table_base));
    }
    auto *call = B.CreateCall(dispatch,
        {fn->getArg(0), target, fn->getArg(2)});
    B.CreateRet(call);

    // default_bb: fallback dispatch
    B.SetInsertPoint(def_bb);
    auto *def_call = B.CreateCall(dispatch,
        {fn->getArg(0), llvm::ConstantInt::get(i64Ty, 0), fn->getArg(2)});
    B.CreateRet(def_call);

    return fn;
  }

  llvm::Function *createJumpTableFunctionWithSharedReturn(
      llvm::Module &M, const char *name, uint64_t table_base,
      unsigned stride, unsigned num_entries) {
    auto *fn = llvm::Function::Create(getLiftedFnType(),
                                      llvm::GlobalValue::ExternalLinkage,
                                      name, &M);
    auto *dispatch = declareDispatch(M);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    auto *jt_bb = llvm::BasicBlock::Create(Ctx, "jt_bb", fn);
    auto *def_bb = llvm::BasicBlock::Create(Ctx, "default_bb", fn);
    auto *join_bb = llvm::BasicBlock::Create(Ctx, "common.ret", fn);

    auto *idx = fn->getArg(1);

    llvm::IRBuilder<> B(entry);
    auto *cmp = B.CreateICmpULT(idx,
        llvm::ConstantInt::get(i64Ty, num_entries));
    B.CreateCondBr(cmp, jt_bb, def_bb);

    B.SetInsertPoint(jt_bb);
    llvm::Value *addr;
    if (stride == 8) {
      auto *shifted = B.CreateShl(idx, llvm::ConstantInt::get(i64Ty, 3));
      addr = B.CreateAdd(shifted,
                         llvm::ConstantInt::get(i64Ty, table_base));
    } else {
      auto *shifted = B.CreateShl(idx, llvm::ConstantInt::get(i64Ty, 2));
      addr = B.CreateAdd(shifted,
                         llvm::ConstantInt::get(i64Ty, table_base));
    }
    auto *ptr = B.CreateIntToPtr(addr, ptrTy);
    auto *target = B.CreateLoad(i64Ty, ptr);
    auto *jt_call = B.CreateCall(dispatch,
        {fn->getArg(0), target, fn->getArg(2)});
    B.CreateBr(join_bb);

    B.SetInsertPoint(def_bb);
    auto *def_call = B.CreateCall(dispatch,
        {fn->getArg(0), llvm::ConstantInt::get(i64Ty, 0), fn->getArg(2)});
    B.CreateBr(join_bb);

    B.SetInsertPoint(join_bb);
    auto *phi = B.CreatePHI(ptrTy, 2);
    phi->addIncoming(jt_call, jt_bb);
    phi->addIncoming(def_call, def_bb);
    B.CreateRet(phi);

    return fn;
  }

  llvm::Function *createDynamicBaseRVATableFunction(
      llvm::Module &M, const char *name, uint64_t table_offset,
      unsigned num_entries) {
    auto *fn = llvm::Function::Create(getLiftedFnType(),
                                      llvm::GlobalValue::ExternalLinkage,
                                      name, &M);
    auto *dispatch = declareDispatch(M);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    auto *jt_bb = llvm::BasicBlock::Create(Ctx, "jt_bb", fn);
    auto *def_bb = llvm::BasicBlock::Create(Ctx, "default_bb", fn);
    auto *join_bb = llvm::BasicBlock::Create(Ctx, "common.ret", fn);

    llvm::IRBuilder<> B(entry);
    auto *base = B.CreatePtrToInt(fn->getArg(0), i64Ty, "base");
    auto *idx = fn->getArg(1);
    auto *masked_idx = B.CreateAnd(idx, llvm::ConstantInt::get(i64Ty, 15));
    auto *cmp = B.CreateICmpULT(masked_idx,
        llvm::ConstantInt::get(i64Ty, num_entries));
    B.CreateCondBr(cmp, jt_bb, def_bb);

    B.SetInsertPoint(jt_bb);
    auto *scaled = B.CreateShl(masked_idx, llvm::ConstantInt::get(i64Ty, 2));
    auto *table_addr = B.CreateAdd(
        B.CreateAdd(base, scaled),
        llvm::ConstantInt::get(i64Ty, table_offset));
    auto *ptr = B.CreateIntToPtr(table_addr, ptrTy);
    auto *target_raw = B.CreateLoad(i32Ty, ptr);
    auto *target = B.CreateAdd(base, B.CreateZExt(target_raw, i64Ty));
    auto *jt_call = B.CreateCall(dispatch,
        {fn->getArg(0), target, fn->getArg(2)});
    B.CreateBr(join_bb);

    B.SetInsertPoint(def_bb);
    auto *def_call = B.CreateCall(dispatch,
        {fn->getArg(0), llvm::ConstantInt::get(i64Ty, 0), fn->getArg(2)});
    B.CreateBr(join_bb);

    B.SetInsertPoint(join_bb);
    auto *phi = B.CreatePHI(ptrTy, 2);
    phi->addIncoming(jt_call, jt_bb);
    phi->addIncoming(def_call, def_bb);
    B.CreateRet(phi);

    return fn;
  }

  llvm::Function *createMaskedGuardedDefaultJumpTableFunction(
      llvm::Module &M, const char *name, uint64_t table_base,
      unsigned stride, unsigned num_entries, unsigned mask) {
    auto *fn = llvm::Function::Create(getLiftedFnType(),
                                      llvm::GlobalValue::ExternalLinkage,
                                      name, &M);
    auto *dispatch = declareDispatch(M);

    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *i8Ty = llvm::Type::getInt8Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
    auto *jt_bb = llvm::BasicBlock::Create(Ctx, "jt_bb", fn);
    auto *def_bb = llvm::BasicBlock::Create(Ctx, "default_bb", fn);

    llvm::IRBuilder<> B(entry);
    auto *masked_idx =
        B.CreateAnd(fn->getArg(1), llvm::ConstantInt::get(i64Ty, mask));
    auto *eq_last = B.CreateICmpEQ(
        masked_idx, llvm::ConstantInt::get(i64Ty, num_entries - 1));
    auto *lt_last = B.CreateICmpULT(
        masked_idx, llvm::ConstantInt::get(i64Ty, num_entries - 1));
    auto *within = B.CreateOr(B.CreateZExt(eq_last, i8Ty),
                              B.CreateZExt(lt_last, i8Ty));
    auto *go_default =
        B.CreateICmpEQ(within, llvm::ConstantInt::get(i8Ty, 0));
    B.CreateCondBr(go_default, def_bb, jt_bb);

    B.SetInsertPoint(jt_bb);
    llvm::Value *addr;
    if (stride == 8) {
      auto *shifted = B.CreateShl(masked_idx, llvm::ConstantInt::get(i64Ty, 3));
      addr = B.CreateAdd(shifted, llvm::ConstantInt::get(i64Ty, table_base));
    } else {
      auto *shifted = B.CreateShl(masked_idx, llvm::ConstantInt::get(i64Ty, 2));
      addr = B.CreateAdd(shifted, llvm::ConstantInt::get(i64Ty, table_base));
    }
    auto *ptr = B.CreateIntToPtr(addr, ptrTy);
    auto *load_ty = (stride == 4) ? llvm::Type::getInt32Ty(Ctx) : i64Ty;
    auto *target_raw = B.CreateLoad(load_ty, ptr);
    llvm::Value *target = target_raw;
    if (stride == 4) {
      target = B.CreateAdd(B.CreateSExt(target_raw, i64Ty),
                           llvm::ConstantInt::get(i64Ty, table_base));
    }
    auto *call = B.CreateCall(dispatch,
        {fn->getArg(0), target, fn->getArg(2)});
    B.CreateRet(call);

    B.SetInsertPoint(def_bb);
    B.CreateRet(fn->getArg(2));

    return fn;
  }
};

// Test: 8-byte stride jump table with 3 entries, all pointing to valid blocks.
TEST_F(JumpTableConcretizerTest, AbsoluteTable8ByteStride) {
  auto M = createModule();

  // Set up binary memory: 3 entries at base 0x1000, stride 8.
  // Entries: 0x2000, 0x3000, 0x4000.
  uint64_t entries[] = {0x2000, 0x3000, 0x4000};
  mem_map.addRegion(0x1000, reinterpret_cast<const uint8_t *>(entries),
                    sizeof(entries), /*read_only=*/true);
  mem_map.setImageBase(0x1000);
  mem_map.setImageSize(0x10000);

  // Create target functions so buildSwitchFromEntries can resolve them.
  // The LiftedFunctionAnalysis scans for sub_<hex> functions with the
  // lifted signature.
  for (uint64_t va : {0x2000ULL, 0x3000ULL, 0x4000ULL}) {
    char name[64];
    snprintf(name, sizeof(name), "sub_%llx", (unsigned long long)va);
    auto *target = llvm::Function::Create(getLiftedFnType(),
        llvm::GlobalValue::ExternalLinkage, name, *M);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> TB(bb);
    TB.CreateRet(target->getArg(2));
  }

  auto *fn = createJumpTableFunction(*M, "sub_140001000", 0x1000, 8, 3);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  // The dispatch_jump in jt_bb should be replaced with a switch.
  bool found_switch = false;
  for (auto &BB : *fn) {
    if (BB.getTerminator() && llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      found_switch = true;
  }
  EXPECT_TRUE(found_switch);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: No dispatch_jump in function — pass is a no-op.
TEST_F(JumpTableConcretizerTest, NoDispatchIsNoOp) {
  auto M = createModule();

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *fnTy = llvm::FunctionType::get(i64Ty, {}, false);
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "regular", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(llvm::ConstantInt::get(i64Ty, 42));

  runPass(fn);

  // Function should be unchanged.
  EXPECT_EQ(fn->size(), 1u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Test: Constant target dispatch_jump is NOT handled (that's for resolution).
TEST_F(JumpTableConcretizerTest, ConstantTargetSkipped) {
  auto M = createModule();

  auto *dispatch = declareDispatch(*M);
  auto *fn = llvm::Function::Create(getLiftedFnType(),
                                    llvm::GlobalValue::ExternalLinkage,
                                    "sub_test", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(entry);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *call = B.CreateCall(dispatch,
      {fn->getArg(0), llvm::ConstantInt::get(i64Ty, 0x5000), fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  // Constant dispatch should not be touched.
  bool found_dispatch = false;
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *ci = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (ci->getCalledFunction() &&
            ci->getCalledFunction()->getName() == "__omill_dispatch_jump")
          found_dispatch = true;
      }
    }
  }
  EXPECT_TRUE(found_dispatch);
}

// Test: Table with unreadable memory — no switch emitted.
TEST_F(JumpTableConcretizerTest, UnreadableTableNoSwitch) {
  auto M = createModule();

  // Don't add any memory region — the table base is unmapped.
  mem_map.setImageBase(0x1000);
  mem_map.setImageSize(0x10000);

  auto *fn = createJumpTableFunction(*M, "sub_test2", 0x9000, 8, 3);
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  // No switch should be created — table is unreadable.
  bool found_switch = false;
  for (auto &BB : *fn) {
    if (BB.getTerminator() && llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      found_switch = true;
  }
  EXPECT_FALSE(found_switch);
}

// Test: 4-byte stride RVA table.
TEST_F(JumpTableConcretizerTest, RVATable4ByteStride) {
  auto M = createModule();

  // 4-byte RVA table at 0x5000.  image_base = 0x5000.
  // Entries (as int32 RVAs): 0x100, 0x200, 0x300 → VAs: 0x5100, 0x5200, 0x5300
  int32_t rva_entries[] = {0x100, 0x200, 0x300};
  mem_map.addRegion(0x5000, reinterpret_cast<const uint8_t *>(rva_entries),
                    sizeof(rva_entries), /*read_only=*/true);
  mem_map.setImageBase(0x5000);
  mem_map.setImageSize(0x10000);

  // Create target functions at the resolved VAs.
  for (uint64_t va : {0x5100ULL, 0x5200ULL, 0x5300ULL}) {
    char name[64];
    snprintf(name, sizeof(name), "sub_%llx", (unsigned long long)va);
    auto *target = llvm::Function::Create(getLiftedFnType(),
        llvm::GlobalValue::ExternalLinkage, name, *M);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> TB(bb);
    TB.CreateRet(target->getArg(2));
  }

  auto *fn = createJumpTableFunction(*M, "sub_rva", 0x5000, 4, 3);
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  // Should emit a switch even with 4-byte RVA entries.
  bool found_switch = false;
  for (auto &BB : *fn) {
    if (BB.getTerminator() && llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      found_switch = true;
  }
  EXPECT_TRUE(found_switch);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(JumpTableConcretizerTest, SharedReturnJoinAfterDispatch) {
  auto M = createModule();

  uint64_t entries[] = {0x2000, 0x3000, 0x4000};
  mem_map.addRegion(0x1000, reinterpret_cast<const uint8_t *>(entries),
                    sizeof(entries), /*read_only=*/true);
  mem_map.setImageBase(0x1000);
  mem_map.setImageSize(0x10000);

  for (uint64_t va : {0x2000ULL, 0x3000ULL, 0x4000ULL}) {
    char name[64];
    snprintf(name, sizeof(name), "sub_%llx", (unsigned long long)va);
    auto *target = llvm::Function::Create(getLiftedFnType(),
        llvm::GlobalValue::ExternalLinkage, name, *M);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> TB(bb);
    TB.CreateRet(target->getArg(2));
  }

  auto *fn = createJumpTableFunctionWithSharedReturn(
      *M, "sub_join", 0x1000, 8, 3);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  bool found_switch = false;
  bool found_dispatch = false;
  for (auto &BB : *fn) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      found_switch = true;
    for (auto &I : BB) {
      if (auto *ci = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (ci->getCalledFunction() &&
            ci->getCalledFunction()->getName() == "__omill_dispatch_jump")
          found_dispatch = true;
      }
    }
  }
  EXPECT_TRUE(found_switch);
  EXPECT_TRUE(found_dispatch);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(JumpTableConcretizerTest, DynamicBaseRVATableSharedReturn) {
  auto M = createModule();

  int32_t rva_entries[] = {
      0x100, 0x200, 0x300, 0x100, 0x200, 0x300, 0x100, 0x200,
      0x300, 0x100, 0x200, 0x300, 0x100, 0x200, 0x300, 0x100};
  mem_map.addRegion(0x6000, reinterpret_cast<const uint8_t *>(rva_entries),
                    sizeof(rva_entries), /*read_only=*/true);
  mem_map.setImageBase(0x5000);
  mem_map.setImageSize(0x10000);

  for (uint64_t va : {0x5100ULL, 0x5200ULL, 0x5300ULL}) {
    char name[64];
    snprintf(name, sizeof(name), "sub_%llx", (unsigned long long)va);
    auto *target = llvm::Function::Create(getLiftedFnType(),
        llvm::GlobalValue::ExternalLinkage, name, *M);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> TB(bb);
    TB.CreateRet(target->getArg(2));
  }

  auto *fn = createDynamicBaseRVATableFunction(
      *M, "sub_dynamic_base", /*table_offset=*/0x1000, 3);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  bool found_switch = false;
  for (auto &BB : *fn) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      found_switch = true;
  }
  if (!found_switch)
    M->print(llvm::errs(), nullptr);
  EXPECT_TRUE(found_switch);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(JumpTableConcretizerTest, GuardedMaskedDefaultUsesTighterPrefixBound) {
  auto M = createModule();

  int32_t rva_entries[] = {
      0x100, 0x120, 0x140, 0x160, 0x180,
      0x1A0, 0x1C0, 0x1E0, 0x200, 0x220,
      0x240, 0x260, 0x280, 0x2A0, 0x2C0,
      0x40000000};
  mem_map.addRegion(0x7000, reinterpret_cast<const uint8_t *>(rva_entries),
                    sizeof(rva_entries), /*read_only=*/true);
  mem_map.setImageBase(0x7000);
  mem_map.setImageSize(0x10000);

  for (uint64_t va : {0x7100ULL, 0x7120ULL, 0x7140ULL, 0x7160ULL, 0x7180ULL,
                      0x71A0ULL, 0x71C0ULL, 0x71E0ULL, 0x7200ULL, 0x7220ULL,
                      0x7240ULL, 0x7260ULL, 0x7280ULL, 0x72A0ULL, 0x72C0ULL}) {
    char name[64];
    snprintf(name, sizeof(name), "sub_%llx", (unsigned long long)va);
    auto *target = llvm::Function::Create(getLiftedFnType(),
        llvm::GlobalValue::ExternalLinkage, name, *M);
    auto *bb = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> TB(bb);
    TB.CreateRet(target->getArg(2));
  }

  auto *fn = createMaskedGuardedDefaultJumpTableFunction(
      *M, "sub_guarded_masked", 0x7000, 4, 15, 15);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  llvm::SwitchInst *switch_inst = nullptr;
  unsigned dispatch_calls = 0;
  for (auto &BB : *fn) {
    if (auto *SW = llvm::dyn_cast<llvm::SwitchInst>(BB.getTerminator()))
      switch_inst = SW;
    for (auto &I : BB) {
      if (auto *ci = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (ci->getCalledFunction() &&
            ci->getCalledFunction()->getName() == "__omill_dispatch_jump") {
          ++dispatch_calls;
        }
      }
    }
  }

  ASSERT_NE(switch_inst, nullptr);
  EXPECT_EQ(switch_inst->getNumCases(), 15u);
  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace
