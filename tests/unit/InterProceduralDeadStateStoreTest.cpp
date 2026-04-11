#include "omill/Passes/InterProceduralDeadStateStore.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"

#include <gtest/gtest.h>

namespace {

class InterProceduralDeadStateStoreTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  // Test State offsets (match fixture in InterProceduralConstPropTest
  // where useful; extended with x86 flag offsets).
  static constexpr unsigned kRAX = 0;
  static constexpr unsigned kRBX = 8;
  static constexpr unsigned kRCX = 16;
  static constexpr unsigned kRDX = 24;
  static constexpr unsigned kRSI = 32;
  static constexpr unsigned kRDI = 40;
  static constexpr unsigned kRSP = 48;
  static constexpr unsigned kRBP = 56;
  static constexpr unsigned kR8 = 64;
  static constexpr unsigned kR9 = 72;

  // Flags — 1 byte each, off the end of the GPR block.
  static constexpr unsigned kCF = 128;
  static constexpr unsigned kPF = 129;
  static constexpr unsigned kAF = 130;
  static constexpr unsigned kZF = 131;
  static constexpr unsigned kSF = 132;
  static constexpr unsigned kOF = 133;

  // XMM0 at 160 (16 bytes).
  static constexpr unsigned kXMM0 = 160;

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

    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *bb_fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    auto *bb_fn = llvm::Function::Create(
        bb_fn_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
    auto *bb_entry = llvm::BasicBlock::Create(Ctx, "entry", bb_fn);
    llvm::IRBuilder<> BBB(bb_entry);
    auto *bb_state = bb_fn->getArg(0);

    struct RegDef {
      const char *name;
      unsigned offset;
    };
    RegDef regs[] = {
        {"RAX", kRAX}, {"RBX", kRBX}, {"RCX", kRCX}, {"RDX", kRDX},
        {"RSI", kRSI}, {"RDI", kRDI}, {"RSP", kRSP}, {"RBP", kRBP},
        {"R8", kR8},   {"R9", kR9},
    };
    for (auto &reg : regs) {
      BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, reg.offset, reg.name);
    }
    const char *flags[] = {"CF", "PF", "AF", "ZF", "SF", "OF"};
    unsigned flag_offsets[] = {kCF, kPF, kAF, kZF, kSF, kOF};
    for (unsigned i = 0; i < 6; ++i) {
      BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, flag_offsets[i],
                             flags[i]);
    }
    BBB.CreateConstGEP1_64(BBB.getInt8Ty(), bb_state, kXMM0, "XMM0");
    BBB.CreateRet(bb_fn->getArg(2));

    return M;
  }

  llvm::Function *makeLifted(llvm::Module &M, const char *name) {
    return llvm::Function::Create(
        liftedFnTy(), llvm::Function::ExternalLinkage, name, M);
  }

  /// store i8 %v, ptr (GEP %state, off)
  void storeFlag(llvm::IRBuilder<> &B, llvm::Value *state, unsigned off,
                 uint8_t val) {
    auto *gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), state, off);
    B.CreateStore(B.getInt8(val), gep);
  }

  /// store i64 %v, ptr (GEP %state, off)
  void storeGPR(llvm::IRBuilder<> &B, llvm::Value *state, unsigned off,
                uint64_t val) {
    auto *gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), state, off);
    B.CreateStore(B.getInt64(val), gep);
  }

  /// load i8, ptr (GEP %state, off) — returned and stored into RAX to
  /// give the value a use the optimizer can't trivially kill.
  void loadFlagAndUse(llvm::IRBuilder<> &B, llvm::Value *state, unsigned off) {
    auto *gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), state, off);
    auto *val = B.CreateLoad(B.getInt8Ty(), gep);
    auto *zext = B.CreateZExt(val, B.getInt64Ty());
    auto *rax_gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), state, kRAX);
    B.CreateStore(zext, rax_gep);
  }

  void loadGPRAndUse(llvm::IRBuilder<> &B, llvm::Value *state, unsigned off) {
    auto *gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), state, off);
    auto *val = B.CreateLoad(B.getInt64Ty(), gep);
    auto *rax_gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), state, kRAX);
    B.CreateStore(val, rax_gep);
  }

  /// Emit `%r = musttail call @callee(%state, %pc, %mem); ret %r`
  void emitMusttailRet(llvm::IRBuilder<> &B, llvm::Function *callee,
                       llvm::Function *caller) {
    auto *call = B.CreateCall(
        callee,
        {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(call);
  }

  unsigned countStoresToOffset(llvm::Function &F, unsigned offset) {
    unsigned count = 0;
    auto &DL = F.getParent()->getDataLayout();
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!SI) continue;
        llvm::Value *ptr = SI->getPointerOperand();
        llvm::APInt ap(64, 0);
        llvm::Value *base = ptr;
        int64_t total = 0;
        while (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
          llvm::APInt local(64, 0);
          if (!GEP->accumulateConstantOffset(DL, local)) break;
          total += local.getSExtValue();
          base = GEP->getPointerOperand();
        }
        if (base == F.getArg(0) && total == (int64_t)offset)
          ++count;
      }
    }
    return count;
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
    MPM.addPass(omill::InterProceduralDeadStateStorePass());
    return MPM.run(M, MAM);
  }
};

TEST_F(InterProceduralDeadStateStoreTest, LinearChainEliminatesDeadFlag) {
  auto M = createModule();
  // Callee: loads ZF.
  auto *callee = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", callee));
    loadFlagAndUse(B, callee->getArg(0), kZF);
    B.CreateRet(callee->getArg(2));
  }
  // Caller: stores AF=0, then musttails into callee.
  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeFlag(B, caller->getArg(0), kAF, 0);
    emitMusttailRet(B, callee, caller);
  }
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  EXPECT_EQ(countStoresToOffset(*caller, kAF), 0u);
}

TEST_F(InterProceduralDeadStateStoreTest, LinearChainPreservesLive) {
  auto M = createModule();
  auto *callee = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", callee));
    loadGPRAndUse(B, callee->getArg(0), kRCX);
    B.CreateRet(callee->getArg(2));
  }
  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeGPR(B, caller->getArg(0), kRCX, 0xdead);
    emitMusttailRet(B, callee, caller);
  }
  runPass(*M);
  EXPECT_EQ(countStoresToOffset(*caller, kRCX), 1u);
}

TEST_F(InterProceduralDeadStateStoreTest, MusttailThreeHopsTransitiveDead) {
  auto M = createModule();
  // c reads only CF.
  auto *c = makeLifted(*M, "sub_403000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", c));
    loadFlagAndUse(B, c->getArg(0), kCF);
    B.CreateRet(c->getArg(2));
  }
  // b stores OF, then musttails c.
  auto *b = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", b));
    storeFlag(B, b->getArg(0), kOF, 0);
    emitMusttailRet(B, c, b);
  }
  // a stores OF, then musttails b.
  auto *a = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", a));
    storeFlag(B, a->getArg(0), kOF, 0);
    emitMusttailRet(B, b, a);
  }

  runPass(*M);

  EXPECT_EQ(countStoresToOffset(*a, kOF), 0u);
  EXPECT_EQ(countStoresToOffset(*b, kOF), 0u);
}

TEST_F(InterProceduralDeadStateStoreTest, MusttailThreeHopsLiveAtTail) {
  auto M = createModule();
  auto *c = makeLifted(*M, "sub_403000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", c));
    loadFlagAndUse(B, c->getArg(0), kSF);
    B.CreateRet(c->getArg(2));
  }
  auto *b = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", b));
    emitMusttailRet(B, c, b);
  }
  auto *a = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", a));
    storeFlag(B, a->getArg(0), kSF, 1);
    emitMusttailRet(B, b, a);
  }

  runPass(*M);

  EXPECT_EQ(countStoresToOffset(*a, kSF), 1u);
}

TEST_F(InterProceduralDeadStateStoreTest, IndirectCallWidens) {
  // An indirect call (no resolvable callee) must widen TLI to `all`, so
  // stores before the call are preserved. Distinct from a dispatch
  // intrinsic with a non-constant target, which is treated as a
  // terminal handoff in --no-abi mode (see DispatchUnresolvedIsTerminal).
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeFlag(B, caller->getArg(0), kCF, 1);
    // Construct an indirect call via inttoptr — getCalledFunction()
    // returns nullptr, triggering the `indirect` widening path.
    auto *fnptr = B.CreateIntToPtr(B.getInt64(0x1000), ptr_ty);
    auto *call = B.CreateCall(
        fn_ty, fnptr,
        {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);
  EXPECT_EQ(countStoresToOffset(*caller, kCF), 1u);
}

TEST_F(InterProceduralDeadStateStoreTest, DispatchUnresolvedIsTerminal) {
  // `__omill_dispatch_call` with a non-constant target is a runtime
  // handoff in --no-abi mode; dead stores before it are eliminable.
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *dispatch_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *dispatch = llvm::Function::Create(
      dispatch_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call",
      *M);

  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeFlag(B, caller->getArg(0), kCF, 1);
    // Non-constant target_pc (arg1) forces the "unresolved" branch.
    auto *dyn_pc = B.CreateAdd(caller->getArg(1), B.getInt64(5));
    auto *call = B.CreateCall(
        dispatch, {caller->getArg(0), dyn_pc, caller->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);
  EXPECT_EQ(countStoresToOffset(*caller, kCF), 0u);
}

TEST_F(InterProceduralDeadStateStoreTest, UnknownExternalPreserves) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ext_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *ext = llvm::Function::Create(
      ext_ty, llvm::Function::ExternalLinkage, "some_unknown_helper", *M);

  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeFlag(B, caller->getArg(0), kAF, 1);
    auto *call = B.CreateCall(
        ext, {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(call);
  }
  runPass(*M);
  EXPECT_EQ(countStoresToOffset(*caller, kAF), 1u);
}

TEST_F(InterProceduralDeadStateStoreTest, NativeExternalEliminates) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  // External taking no State-derived pointer arg — just an i64 arg.
  auto *ext_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *ext = llvm::Function::Create(
      ext_ty, llvm::Function::ExternalLinkage, "KERNEL32_GetProcAddress", *M);

  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeFlag(B, caller->getArg(0), kAF, 0);
    storeFlag(B, caller->getArg(0), kZF, 0);
    B.CreateCall(ext, {B.getInt64(0x1234)});
    B.CreateRet(caller->getArg(2));
  }

  runPass(*M);
  EXPECT_EQ(countStoresToOffset(*caller, kAF), 0u);
  EXPECT_EQ(countStoresToOffset(*caller, kZF), 0u);
}

TEST_F(InterProceduralDeadStateStoreTest, IdempotencyAttribute) {
  auto M = createModule();
  auto *callee = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", callee));
    loadFlagAndUse(B, callee->getArg(0), kZF);
    B.CreateRet(callee->getArg(2));
  }
  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    storeFlag(B, caller->getArg(0), kAF, 0);
    emitMusttailRet(B, callee, caller);
  }

  runPass(*M);
  EXPECT_TRUE(caller->hasFnAttribute("omill.ipdse_done"));
  EXPECT_TRUE(callee->hasFnAttribute("omill.ipdse_done"));

  // Second run is a no-op.
  auto store_count_before = countStoresToOffset(*caller, kAF);
  runPass(*M);
  EXPECT_EQ(countStoresToOffset(*caller, kAF), store_count_before);
}

TEST_F(InterProceduralDeadStateStoreTest, PartialOverlapPreserves) {
  auto M = createModule();
  // Callee reads 1 byte inside XMM0 (say at kXMM0+8).
  auto *callee = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", callee));
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), callee->getArg(0),
                                     kXMM0 + 8);
    auto *val = B.CreateLoad(B.getInt8Ty(), gep);
    auto *zext = B.CreateZExt(val, B.getInt64Ty());
    auto *rax_gep =
        B.CreateConstGEP1_64(B.getInt8Ty(), callee->getArg(0), kRAX);
    B.CreateStore(zext, rax_gep);
    B.CreateRet(callee->getArg(2));
  }
  // Caller stores 16 bytes to XMM0 (overlapping the live byte).
  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), caller->getArg(0), kXMM0);
    auto *v128_ty = llvm::FixedVectorType::get(B.getInt8Ty(), 16);
    auto *zero = llvm::Constant::getNullValue(v128_ty);
    B.CreateStore(zero, gep);
    emitMusttailRet(B, callee, caller);
  }

  runPass(*M);

  // The 16-byte store covers a live byte — must be preserved.
  EXPECT_EQ(countStoresToOffset(*caller, kXMM0), 1u);
}

TEST_F(InterProceduralDeadStateStoreTest, FlagStoreBatchAfterArithmetic) {
  auto M = createModule();
  auto *callee = makeLifted(*M, "sub_402000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", callee));
    loadFlagAndUse(B, callee->getArg(0), kCF);
    B.CreateRet(callee->getArg(2));
  }
  auto *caller = makeLifted(*M, "sub_401000");
  {
    llvm::IRBuilder<> B(llvm::BasicBlock::Create(Ctx, "entry", caller));
    // Six flag stores mimicking ADD's flag writeback.
    storeFlag(B, caller->getArg(0), kPF, 0);
    storeFlag(B, caller->getArg(0), kAF, 0);
    storeFlag(B, caller->getArg(0), kZF, 0);
    storeFlag(B, caller->getArg(0), kSF, 0);
    storeFlag(B, caller->getArg(0), kOF, 0);
    storeFlag(B, caller->getArg(0), kCF, 1);
    emitMusttailRet(B, callee, caller);
  }

  runPass(*M);

  EXPECT_EQ(countStoresToOffset(*caller, kPF), 0u);
  EXPECT_EQ(countStoresToOffset(*caller, kAF), 0u);
  EXPECT_EQ(countStoresToOffset(*caller, kZF), 0u);
  EXPECT_EQ(countStoresToOffset(*caller, kSF), 0u);
  EXPECT_EQ(countStoresToOffset(*caller, kOF), 0u);
  EXPECT_EQ(countStoresToOffset(*caller, kCF), 1u);
}

}  // namespace
