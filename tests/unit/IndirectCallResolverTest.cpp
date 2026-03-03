#include "omill/Passes/IndirectCallResolver.h"

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

class IndirectCallResolverTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;
  omill::BinaryMemoryMap mem_map;
  std::vector<std::unique_ptr<uint8_t[]>> mem_bufs;

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

    MAM.registerPass([this] {
      return omill::BinaryMemoryAnalysis(mem_map);
    });
    MAM.registerPass([] { return omill::LiftedFunctionAnalysis(); });

    (void)MAM.getResult<omill::BinaryMemoryAnalysis>(*M);
    (void)MAM.getResult<omill::LiftedFunctionAnalysis>(*M);

    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::IndirectCallResolverPass());
    FPM.run(*F, FAM);
  }

  /// The standard lifted function type: (State*, i64, Memory*) -> Memory*
  llvm::FunctionType *getLiftedFnType() {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);
    return llvm::FunctionType::get(ptrTy, {ptrTy, i64Ty, ptrTy}, false);
  }

  /// Create __omill_dispatch_call declaration.
  llvm::Function *declareDispatchCall(llvm::Module &M) {
    auto *fn = M.getFunction("__omill_dispatch_call");
    if (fn)
      return fn;
    return llvm::Function::Create(getLiftedFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  "__omill_dispatch_call", &M);
  }

  /// Create __omill_dispatch_jump declaration.
  llvm::Function *declareDispatchJump(llvm::Module &M) {
    auto *fn = M.getFunction("__omill_dispatch_jump");
    if (fn)
      return fn;
    return llvm::Function::Create(getLiftedFnType(),
                                  llvm::GlobalValue::ExternalLinkage,
                                  "__omill_dispatch_jump", &M);
  }

  /// Create a test lifted function with a single BB containing a dispatch call.
  /// Returns {function, dispatch_call_inst}.
  std::pair<llvm::Function *, llvm::CallInst *>
  createDispatchCallFn(llvm::Module &M, const char *name,
                       llvm::Value *targetExpr) {
    auto *fnTy = getLiftedFnType();
    auto *fn = llvm::Function::Create(
        fnTy, llvm::GlobalValue::ExternalLinkage, name, &M);
    auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(BB);

    auto *dispatch = declareDispatchCall(M);
    auto *state = fn->getArg(0);
    auto *mem = fn->getArg(2);

    auto *call = B.CreateCall(dispatch, {state, targetExpr, mem});
    B.CreateRet(call);
    return {fn, call};
  }

  /// Create a test lifted function with dispatch_jump + ret.
  std::pair<llvm::Function *, llvm::CallInst *>
  createDispatchJumpFn(llvm::Module &M, const char *name,
                       llvm::Value *targetExpr) {
    auto *fnTy = getLiftedFnType();
    auto *fn = llvm::Function::Create(
        fnTy, llvm::GlobalValue::ExternalLinkage, name, &M);
    auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
    llvm::IRBuilder<> B(BB);

    auto *dispatch = declareDispatchJump(M);
    auto *state = fn->getArg(0);
    auto *mem = fn->getArg(2);

    auto *call = B.CreateCall(dispatch, {state, targetExpr, mem});
    B.CreateRet(call);
    return {fn, call};
  }

  /// Create inttoptr(i64 const) → ptr, then load i64 from it.
  /// Emits into the given builder.
  llvm::LoadInst *createMemLoad(llvm::IRBuilder<> &B, uint64_t addr) {
    auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptrTy = llvm::PointerType::get(Ctx, 0);
    auto *addr_val = llvm::ConstantInt::get(i64Ty, addr);
    auto *ptr = B.CreateIntToPtr(addr_val, ptrTy);
    return B.CreateLoad(i64Ty, ptr);
  }

  /// Count calls to a named function within F.
  unsigned countCalls(llvm::Function *F, llvm::StringRef callee_name) {
    unsigned n = 0;
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = CI->getCalledFunction())
            if (callee->getName() == callee_name)
              ++n;
    return n;
  }

  /// Find the first call to a named function.
  llvm::CallInst *findCall(llvm::Function *F, llvm::StringRef callee_name) {
    for (auto &BB : *F)
      for (auto &I : BB)
        if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
          if (auto *callee = CI->getCalledFunction())
            if (callee->getName() == callee_name)
              return CI;
    return nullptr;
  }

  /// Check if a constant i64 appears as an operand anywhere in F.
  bool hasConstantI64(llvm::Function *F, uint64_t val) {
    for (auto &BB : *F)
      for (auto &I : BB)
        for (auto &Op : I.operands())
          if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(Op.get()))
            if (CI->getBitWidth() == 64 && CI->getZExtValue() == val)
              return true;
    return false;
  }

  /// Add a little-endian i64 to the memory map.
  /// Buffer is heap-allocated and persisted for the lifetime of the test.
  void addI64(uint64_t addr, uint64_t value) {
    auto buf = std::make_unique<uint8_t[]>(8);
    for (int i = 0; i < 8; ++i)
      buf[i] = static_cast<uint8_t>((value >> (i * 8)) & 0xFF);
    auto *ptr = buf.get();
    mem_bufs.push_back(std::move(buf));
    mem_map.addRegion(addr, ptr, 8);
  }

  /// Add a little-endian i32 to the memory map.
  void addI32(uint64_t addr, uint32_t value) {
    auto buf = std::make_unique<uint8_t[]>(4);
    for (int i = 0; i < 4; ++i)
      buf[i] = static_cast<uint8_t>((value >> (i * 8)) & 0xFF);
    auto *ptr = buf.get();
    mem_bufs.push_back(std::move(buf));
    mem_map.addRegion(addr, ptr, 4);
  }
};

// ===----------------------------------------------------------------------===
// Test 1: dispatch_call with load(inttoptr(const)) → resolved via memory read
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, LoadFromConstantAddress_ResolvesToLiftedFn) {
  auto M = createModule();

  // Binary memory: [0x140008000] = 0x140001000 (a lifted function address)
  addI64(0x140008000, 0x140001000);

  // Create the target lifted function.
  auto *target = llvm::Function::Create(getLiftedFnType(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_140001000", *M);
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "entry", target);
  llvm::IRBuilder<> targetB(targetBB);
  targetB.CreateRet(target->getArg(2));

  // Create test function: dispatch_call(state, load(inttoptr(0x140008000)), mem)
  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *load = createMemLoad(B, 0x140008000);
  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), load, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // dispatch_call should be replaced with a direct call to sub_140001000.
  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140001000"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 2: Chained memory read — load(inttoptr(load(inttoptr(const)) + offset))
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, ChainedMemoryRead_VtableDispatch) {
  auto M = createModule();

  // Binary memory layout:
  //   [0x140008000] = 0x14000A000 (vtable pointer)
  //   [0x14000A000 + 0x10] = 0x140003000 (vtable entry)
  addI64(0x140008000, 0x14000A000);
  addI64(0x14000A010, 0x140003000);

  // Create target lifted function.
  auto *target = llvm::Function::Create(getLiftedFnType(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_140003000", *M);
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "entry", target);
  llvm::IRBuilder<> targetB(targetBB);
  targetB.CreateRet(target->getArg(2));

  // Create test function:
  //   %vtable = load i64, ptr inttoptr(i64 0x140008000 to ptr)
  //   %entry_addr = add i64 %vtable, 16
  //   %target = load i64, ptr inttoptr(i64 %entry_addr to ptr)
  //   dispatch_call(state, %target, mem)
  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);

  // load vtable pointer
  auto *vtable_addr = llvm::ConstantInt::get(i64Ty, 0x140008000);
  auto *vtable_ptr = B.CreateIntToPtr(vtable_addr, ptrTy);
  auto *vtable = B.CreateLoad(i64Ty, vtable_ptr);

  // add offset
  auto *entry_addr = B.CreateAdd(vtable, llvm::ConstantInt::get(i64Ty, 0x10));

  // load function pointer
  auto *entry_ptr = B.CreateIntToPtr(entry_addr, ptrTy);
  auto *fptr = B.CreateLoad(i64Ty, entry_ptr);

  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), fptr, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Should resolve to direct call.
  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140003000"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 3: XOR deobfuscation — load(const) xor key → function pointer
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, XorDeobfuscation) {
  auto M = createModule();

  // Binary memory: [0x140005000] = 0x140001000 ^ 0xDEADBEEF = 0x14DEADAFEF
  uint64_t real_target = 0x140001000;
  uint64_t xor_key = 0xDEADBEEF;
  uint64_t obfuscated = real_target ^ xor_key;
  addI64(0x140005000, obfuscated);

  // Create target.
  auto *target = llvm::Function::Create(getLiftedFnType(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_140001000", *M);
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "entry", target);
  llvm::IRBuilder<> targetB(targetBB);
  targetB.CreateRet(target->getArg(2));

  // Create test: dispatch_call(state, load(0x140005000) ^ 0xDEADBEEF, mem)
  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *loaded = createMemLoad(B, 0x140005000);
  auto *deobf = B.CreateXor(loaded, llvm::ConstantInt::get(i64Ty, xor_key));

  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), deobf, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140001000"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 4: Already-constant target is skipped (no crash, no change)
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, AlreadyConstant_Skipped) {
  auto M = createModule();

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0),
                                       llvm::ConstantInt::get(i64Ty, 0x401000),
                                       fn->getArg(2)});
  B.CreateRet(call);

  runPass(fn);

  // Should be untouched (already constant, handled by other passes).
  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 5: Truly dynamic target (load from unknown pointer) — left unchanged
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, DynamicTarget_LeftUnchanged) {
  auto M = createModule();

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  // Target is a load from a dynamic pointer (arg 0 cast to i64*) — truly
  // dynamic and unresolvable.  We can't use arg 1 because arg 1 of a
  // sub_<hex> function is the entry PC, which evaluateToConstant resolves.
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dynamic_target = B.CreateLoad(i64_ty, fn->getArg(0), "dyn_target");
  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0),
                                       dynamic_target,
                                       fn->getArg(2)});
  B.CreateRet(call);

  runPass(fn);

  // Should be untouched.
  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 6: dispatch_jump resolved to intra-function branch
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, DispatchJump_IntraFunctionBranch) {
  auto M = createModule();

  // Memory: [0x140005000] = 0x140002010 (a block PC within the function)
  addI64(0x140005000, 0x140002010);

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);

  // Create target block.
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "block_140002010", fn);
  {
    llvm::IRBuilder<> B(targetBB);
    B.CreateRet(fn->getArg(2));
  }

  // Create entry block with dispatch_jump.
  auto *entryBB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  // Move entry before target.
  entryBB->moveBefore(targetBB);

  llvm::IRBuilder<> B(entryBB);
  auto *loaded = createMemLoad(B, 0x140005000);
  auto *dispatch = declareDispatchJump(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), loaded, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // dispatch_jump should be gone, replaced with a branch.
  EXPECT_EQ(countCalls(fn, "__omill_dispatch_jump"), 0u);

  // Entry block should end with a branch to the target block.
  auto *term = entryBB->getTerminator();
  ASSERT_NE(term, nullptr);
  auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
  ASSERT_NE(br, nullptr);
  EXPECT_EQ(br->getSuccessor(0), targetBB);
}

// ===----------------------------------------------------------------------===
// Test 7: dispatch_jump resolved to inter-function musttail call
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, DispatchJump_InterFunctionTailCall) {
  auto M = createModule();

  // Memory: [0x140005000] = 0x140003000 (another lifted function)
  addI64(0x140005000, 0x140003000);

  auto *target = llvm::Function::Create(getLiftedFnType(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_140003000", *M);
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "entry", target);
  llvm::IRBuilder<> targetB(targetBB);
  targetB.CreateRet(target->getArg(2));

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *loaded = createMemLoad(B, 0x140005000);
  auto *dispatch = declareDispatchJump(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), loaded, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // dispatch_jump should be replaced with a musttail call.
  EXPECT_EQ(countCalls(fn, "__omill_dispatch_jump"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140003000"), 1u);

  // Verify it's a musttail call.
  auto *resolved_call = findCall(fn, "sub_140003000");
  ASSERT_NE(resolved_call, nullptr);
  EXPECT_EQ(resolved_call->getTailCallKind(), llvm::CallInst::TCK_MustTail);
}

// ===----------------------------------------------------------------------===
// Test 8: Import resolution via memory read
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, ImportResolution) {
  auto M = createModule();

  // Binary memory: [0x140006000] = 0x7FF80001000 (import thunk address)
  addI64(0x140006000, 0x7FF80001000);

  // Register the import.
  mem_map.addImport(0x7FF80001000, "kernel32.dll", "CreateFileW");

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *loaded = createMemLoad(B, 0x140006000);
  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), loaded, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // dispatch_call should still exist but target should be ptrtoint(@CreateFileW).
  auto *resolved = findCall(fn, "__omill_dispatch_call");
  ASSERT_NE(resolved, nullptr);

  auto *target_arg = resolved->getArgOperand(1);
  auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target_arg);
  ASSERT_NE(ptoi, nullptr);

  auto *import_fn = llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
  ASSERT_NE(import_fn, nullptr);
  EXPECT_EQ(import_fn->getName(), "CreateFileW");
  EXPECT_EQ(import_fn->getDLLStorageClass(),
            llvm::GlobalValue::DLLImportStorageClass);
}

// ===----------------------------------------------------------------------===
// Test 9: Memory address not in map — left unchanged
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, UnmappedAddress_LeftUnchanged) {
  auto M = createModule();

  // No memory at 0x140009000.

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *loaded = createMemLoad(B, 0x140009000);
  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), loaded, fn->getArg(2)});
  B.CreateRet(call);

  runPass(fn);

  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 10: Multiple dispatch calls — both resolved independently
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, MultipleDispatches_BothResolved) {
  auto M = createModule();

  addI64(0x140008000, 0x140001000);
  addI64(0x140008008, 0x140001100);

  auto *t1 = llvm::Function::Create(getLiftedFnType(),
                                    llvm::GlobalValue::ExternalLinkage,
                                    "sub_140001000", *M);
  auto *t1BB = llvm::BasicBlock::Create(Ctx, "entry", t1);
  llvm::IRBuilder<>(t1BB).CreateRet(t1->getArg(2));

  auto *t2 = llvm::Function::Create(getLiftedFnType(),
                                    llvm::GlobalValue::ExternalLinkage,
                                    "sub_140001100", *M);
  auto *t2BB = llvm::BasicBlock::Create(Ctx, "entry", t2);
  llvm::IRBuilder<>(t2BB).CreateRet(t2->getArg(2));

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *load1 = createMemLoad(B, 0x140008000);
  auto *dispatch = declareDispatchCall(*M);
  auto *call1 = B.CreateCall(dispatch, {fn->getArg(0), load1, fn->getArg(2)});

  auto *load2 = createMemLoad(B, 0x140008008);
  auto *call2 = B.CreateCall(dispatch, {fn->getArg(0), load2, fn->getArg(2)});

  B.CreateRet(call2);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140001000"), 1u);
  EXPECT_EQ(countCalls(fn, "sub_140001100"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 11: Add arithmetic on loaded value
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, AddArithmetic_RVAConversion) {
  auto M = createModule();

  // Memory: [0x140005000] = 0x1000 (RVA)
  // Image base = 0x140000000
  // Target = 0x140000000 + 0x1000 = 0x140001000
  addI64(0x140005000, 0x1000);

  auto *target = llvm::Function::Create(getLiftedFnType(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_140001000", *M);
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "entry", target);
  llvm::IRBuilder<>(targetBB).CreateRet(target->getArg(2));

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *rva = createMemLoad(B, 0x140005000);
  auto *target_pc = B.CreateAdd(rva, llvm::ConstantInt::get(i64Ty, 0x140000000));

  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), target_pc, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140001000"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 12: 32-bit load (i32) with zext
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, I32Load_WithZext) {
  auto M = createModule();

  // Memory: [0x140005000] = 0x00001000 (32-bit RVA)
  addI32(0x140005000, 0x1000);

  auto *target = llvm::Function::Create(getLiftedFnType(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_140001000", *M);
  auto *targetBB = llvm::BasicBlock::Create(Ctx, "entry", target);
  llvm::IRBuilder<>(targetBB).CreateRet(target->getArg(2));

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *i32Ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);

  auto *addr = llvm::ConstantInt::get(i64Ty, 0x140005000);
  auto *ptr = B.CreateIntToPtr(addr, ptrTy);
  auto *loaded32 = B.CreateLoad(i32Ty, ptr);
  auto *extended = B.CreateZExt(loaded32, i64Ty);
  auto *target_pc = B.CreateAdd(extended, llvm::ConstantInt::get(i64Ty, 0x140000000));

  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), target_pc, fn->getArg(2)});
  B.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(fn);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  EXPECT_EQ(countCalls(fn, "__omill_dispatch_call"), 0u);
  EXPECT_EQ(countCalls(fn, "sub_140001000"), 1u);
}

// ===----------------------------------------------------------------------===
// Test 13: No target match after resolution — target replaced with constant
// ===----------------------------------------------------------------------===
TEST_F(IndirectCallResolverTest, ResolvedButNoMatch_TargetBecomesConstant) {
  auto M = createModule();

  // Memory: [0x140008000] = 0xDEADBEEF (not a lifted function or import)
  addI64(0x140008000, 0xDEADBEEF);

  auto *fnTy = getLiftedFnType();
  auto *fn = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                    "sub_140002000", *M);
  auto *BB = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B(BB);

  auto *loaded = createMemLoad(B, 0x140008000);
  auto *dispatch = declareDispatchCall(*M);
  auto *call = B.CreateCall(dispatch, {fn->getArg(0), loaded, fn->getArg(2)});
  B.CreateRet(call);

  runPass(fn);

  // dispatch_call remains but target is now constant (for downstream passes).
  auto *resolved = findCall(fn, "__omill_dispatch_call");
  ASSERT_NE(resolved, nullptr);

  auto *target_arg = llvm::dyn_cast<llvm::ConstantInt>(resolved->getArgOperand(1));
  ASSERT_NE(target_arg, nullptr);
  EXPECT_EQ(target_arg->getZExtValue(), 0xDEADBEEFULL);
}

// The forward Monte Carlo interpreter resolves dispatch targets where the
// expression depends on inttoptr stores in a different basic block.
// This simulates a post-SROA VM handler pattern: entry block stores a value
// to a virtual stack slot (inttoptr(RSP + C)), then a later block loads it
// and uses it to compute the dispatch target.  RSP is a single SSA value
// (as produced by OptimizeState/SROA) used across all blocks.
TEST_F(IndirectCallResolverTest, CrossBBIntToPtrForwarding_ForwardMC) {
  auto M = createModule();
  addI64(0x140020000, 0);  // Map target address so BMM validation passes.

  // Target function at 0x140020000.
  auto *target_fn = llvm::Function::Create(
      getLiftedFnType(), llvm::GlobalValue::ExternalLinkage,
      "sub_140020000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  // Caller function.
  auto *fn = llvm::Function::Create(
      getLiftedFnType(), llvm::GlobalValue::ExternalLinkage,
      "sub_140001000", *M);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);

  // BB0: entry — load RSP once (simulating post-SROA single SSA value),
  // then store constant to inttoptr(RSP - 100).
  auto *BB0 = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B0(BB0);
  auto *rsp = B0.CreateLoad(i64Ty,
      B0.CreateGEP(llvm::Type::getInt8Ty(Ctx), fn->getArg(0),
                   B0.getInt64(2312)),
      "rsp");
  auto *slot_addr = B0.CreateSub(rsp, B0.getInt64(100), "slot_addr");
  auto *slot_ptr = B0.CreateIntToPtr(slot_addr, ptrTy);
  B0.CreateStore(B0.getInt64(0x140020000), slot_ptr);
  auto *BB1 = llvm::BasicBlock::Create(Ctx, "dispatch_bb", fn);
  B0.CreateBr(BB1);

  // BB1: dispatch — load from same slot using same RSP SSA value.
  llvm::IRBuilder<> B1(BB1);
  auto *slot_addr2 = B1.CreateSub(rsp, B1.getInt64(100), "slot_addr2");
  auto *slot_ptr2 = B1.CreateIntToPtr(slot_addr2, ptrTy);
  auto *loaded = B1.CreateLoad(i64Ty, slot_ptr2, "dispatch_target");
  auto *dispatch = declareDispatchJump(*M);
  auto *call = B1.CreateCall(dispatch,
      {fn->getArg(0), loaded, fn->getArg(2)});
  B1.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  runPass(fn);

  // The forward MC interpreter should resolve the cross-BB store→load and
  // turn the dispatch_jump into a musttail call to sub_140020000.
  bool found_dispatch = false;
  bool found_tail_call = false;
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (auto *Callee = CI->getCalledFunction()) {
          if (Callee->getName() == "__omill_dispatch_jump")
            found_dispatch = true;
          if (Callee == target_fn)
            found_tail_call = true;
        }
      }
    }
  }
  EXPECT_FALSE(found_dispatch) << "dispatch_jump should be resolved";
  EXPECT_TRUE(found_tail_call) << "should have direct call to sub_140020000";
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

// Forward MC with MBA obfuscation across blocks: store obfuscated value
// to slot, later load and deobfuscate → constant dispatch target.
// Uses single RSP SSA value (post-SROA pattern).
TEST_F(IndirectCallResolverTest, CrossBBWithMBA_ForwardMC) {
  auto M = createModule();
  addI64(0x140030000, 0);  // Map target address so BMM validation passes.

  auto *target_fn = llvm::Function::Create(
      getLiftedFnType(), llvm::GlobalValue::ExternalLinkage,
      "sub_140030000", *M);
  auto *target_entry = llvm::BasicBlock::Create(Ctx, "entry", target_fn);
  llvm::IRBuilder<>(target_entry).CreateRet(target_fn->getArg(2));

  auto *fn = llvm::Function::Create(
      getLiftedFnType(), llvm::GlobalValue::ExternalLinkage,
      "sub_140001000", *M);
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptrTy = llvm::PointerType::get(Ctx, 0);

  // BB0: load RSP once, store (RSP ^ 0xDEAD) to inttoptr(RSP - 200).
  auto *BB0 = llvm::BasicBlock::Create(Ctx, "entry", fn);
  llvm::IRBuilder<> B0(BB0);
  auto *rsp = B0.CreateLoad(i64Ty,
      B0.CreateGEP(llvm::Type::getInt8Ty(Ctx), fn->getArg(0),
                   B0.getInt64(2312)),
      "rsp");
  auto *slot_addr = B0.CreateSub(rsp, B0.getInt64(200), "slot_addr");
  auto *slot_ptr = B0.CreateIntToPtr(slot_addr, ptrTy);
  auto *obfuscated = B0.CreateXor(rsp, B0.getInt64(0xDEAD), "obf_val");
  B0.CreateStore(obfuscated, slot_ptr);
  auto *BB1 = llvm::BasicBlock::Create(Ctx, "dispatch_bb", fn);
  B0.CreateBr(BB1);

  // BB1: load slot, XOR back to recover RSP, add offset → constant target.
  // target = load(slot) ^ 0xDEAD + 0x140030000 - RSP
  // = (RSP ^ 0xDEAD) ^ 0xDEAD + 0x140030000 - RSP
  // = RSP + 0x140030000 - RSP = 0x140030000
  llvm::IRBuilder<> B1(BB1);
  auto *slot_addr2 = B1.CreateSub(rsp, B1.getInt64(200), "slot_addr2");
  auto *slot_ptr2 = B1.CreateIntToPtr(slot_addr2, ptrTy);
  auto *loaded = B1.CreateLoad(i64Ty, slot_ptr2, "loaded");
  auto *deobf = B1.CreateXor(loaded, B1.getInt64(0xDEAD), "deobf");
  auto *target = B1.CreateAdd(
      B1.CreateSub(deobf, rsp, "cancel_rsp"),
      B1.getInt64(0x140030000), "target");
  auto *dispatch = declareDispatchJump(*M);
  auto *call = B1.CreateCall(dispatch,
      {fn->getArg(0), target, fn->getArg(2)});
  B1.CreateRet(call);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  runPass(fn);

  bool found_dispatch = false;
  bool found_tail_call = false;
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (auto *Callee = CI->getCalledFunction()) {
          if (Callee->getName() == "__omill_dispatch_jump")
            found_dispatch = true;
          if (Callee == target_fn)
            found_tail_call = true;
        }
      }
    }
  }
  EXPECT_FALSE(found_dispatch) << "dispatch_jump should be resolved";
  EXPECT_TRUE(found_tail_call) << "should resolve to sub_140030000";
  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

}  // namespace
