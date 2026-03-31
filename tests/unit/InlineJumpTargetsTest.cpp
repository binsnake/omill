#include "omill/Passes/InlineJumpTargets.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class InlineJumpTargetsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Remill lifted function type: (ptr, i64, ptr) -> ptr
  llvm::FunctionType *liftedFnTy() {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  void runPass(llvm::Module &M) {
    llvm::ModulePassManager MPM;
    MPM.addPass(omill::InlineJumpTargetsPass());
    llvm::ModuleAnalysisManager MAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::LoopAnalysisManager LAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::PassBuilder PB;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    MPM.run(M, MAM);
  }

  /// Create __remill_jump declaration.
  llvm::Function *createRemillJump(llvm::Module &M) {
    return llvm::Function::Create(liftedFnTy(), llvm::Function::ExternalLinkage,
                                  "__remill_jump", M);
  }

  /// Create __remill_function_return declaration.
  llvm::Function *createRemillReturn(llvm::Module &M) {
    return llvm::Function::Create(liftedFnTy(), llvm::Function::ExternalLinkage,
                                  "__remill_function_return", M);
  }
};

// ===----------------------------------------------------------------------===
// Test 1: Stub declaration resolved to defined implementation
// ===----------------------------------------------------------------------===

TEST_F(InlineJumpTargetsTest, StubResolvedToDefinition) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  // Declare sub_180001000 (stub).
  auto *stub = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000", *M);
  ASSERT_TRUE(stub->isDeclaration());

  // Define sub_180001000.2 (implementation).
  auto *def = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000.2", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", def);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(def->getArg(2));

  // Create a caller that uses the stub.
  auto *caller = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180002000", *M);
  auto *ce = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> CB(ce);
  auto *result = CB.CreateCall(stub, {caller->getArg(0), caller->getArg(1),
                                      caller->getArg(2)});
  CB.CreateRet(result);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Stub should have been replaced — caller now calls def directly.
  bool calls_def = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() == def)
          calls_def = true;
      }
    }
  }
  EXPECT_TRUE(calls_def) << "Caller should call definition, not stub";
}

// ===----------------------------------------------------------------------===
// Test 2: Non-constant __remill_jump replaced with switch over disconnected
//         block PCs.
// ===----------------------------------------------------------------------===

TEST_F(InlineJumpTargetsTest, JumpLoweredToSwitch) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *jump_fn = createRemillJump(*M);

  // Create lifted function with entry block and two disconnected blocks.
  auto *F = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  // Disconnected blocks named with block_ prefix + hex PC.
  auto *block_a = llvm::BasicBlock::Create(Ctx, "block_180001010", F);
  auto *block_b = llvm::BasicBlock::Create(Ctx, "block_180001020", F);

  // Entry: call __remill_jump with non-constant PC.
  llvm::IRBuilder<> B(entry);
  auto *target = B.CreateLoad(i64_ty, F->getArg(0));  // non-constant
  auto *result = B.CreateCall(jump_fn, {F->getArg(0), target, F->getArg(2)});
  result->addFnAttr(llvm::Attribute::get(
      Ctx, "omill.virtual_exit_disposition", "stay_in_vm"));
  B.CreateRet(result);

  // Disconnected blocks: just return.
  llvm::IRBuilder<> BA(block_a);
  BA.CreateRet(F->getArg(2));
  llvm::IRBuilder<> BB2(block_b);
  BB2.CreateRet(F->getArg(2));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Entry block should now have a switch instruction.
  auto *term = F->getEntryBlock().getTerminator();
  EXPECT_TRUE(llvm::isa<llvm::SwitchInst>(term))
      << "Expected switch after jump lowering, got "
      << (term ? term->getOpcodeName() : "null");

  if (auto *SW = llvm::dyn_cast<llvm::SwitchInst>(term)) {
    EXPECT_GE(SW->getNumCases(), 2u)
        << "Expected at least 2 switch cases for the disconnected blocks";
  }

  llvm::BasicBlock *FallbackBB = nullptr;
  for (auto &BB : *F) {
    if (BB.getName() == "jump_dispatch_fallback") {
      FallbackBB = &BB;
      break;
    }
  }
  ASSERT_NE(FallbackBB, nullptr);
  auto *FallbackCall = llvm::dyn_cast<llvm::CallInst>(&FallbackBB->front());
  ASSERT_NE(FallbackCall, nullptr);
  ASSERT_TRUE(FallbackCall->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(FallbackCall->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "stay_in_vm");
}

TEST_F(InlineJumpTargetsTest, VmExitJumpIsPreservedAsExplicitJump) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *jump_fn = createRemillJump(*M);

  auto *F = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *block_a = llvm::BasicBlock::Create(Ctx, "block_180001010", F);
  auto *block_b = llvm::BasicBlock::Create(Ctx, "block_180001020", F);

  llvm::IRBuilder<> B(entry);
  auto *target = B.CreateLoad(i64_ty, F->getArg(0));
  auto *result = B.CreateCall(jump_fn, {F->getArg(0), target, F->getArg(2)});
  result->addFnAttr(llvm::Attribute::get(
      Ctx, "omill.virtual_exit_disposition",
      "vm_exit_native_exec_unknown_return"));
  result->addFnAttr(
      llvm::Attribute::get(Ctx, "omill.virtual_exit_partial", "1"));
  B.CreateRet(result);

  llvm::IRBuilder<> BA(block_a);
  BA.CreateRet(F->getArg(2));
  llvm::IRBuilder<> BB2(block_b);
  BB2.CreateRet(F->getArg(2));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  EXPECT_TRUE(llvm::isa<llvm::ReturnInst>(F->getEntryBlock().getTerminator()));
  llvm::CallInst *entry_call = nullptr;
  for (auto &I : F->getEntryBlock()) {
    auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
    if (!CI)
      continue;
    if (CI->getCalledFunction() == jump_fn) {
      entry_call = CI;
      break;
    }
  }
  ASSERT_NE(entry_call, nullptr);
  ASSERT_EQ(entry_call->getCalledFunction(), jump_fn);
  ASSERT_TRUE(entry_call->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(entry_call->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_exec_unknown_return");
}

// ===----------------------------------------------------------------------===
// Test 3: __remill_function_return in non-tail position neutralized after
//         inlining.
// ===----------------------------------------------------------------------===

TEST_F(InlineJumpTargetsTest, InlinedReturnNeutralized) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *ret_fn = createRemillReturn(*M);
  auto *jump_fn = createRemillJump(*M);

  // Callee: has a disconnected block and a __remill_jump → will be inlined.
  auto *callee = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180002000", *M);
  auto *ce = llvm::BasicBlock::Create(Ctx, "entry", callee);
  auto *disc = llvm::BasicBlock::Create(Ctx, "block_180002010", callee);

  // Entry: non-constant jump.
  llvm::IRBuilder<> CB(ce);
  auto *target = CB.CreateLoad(i64_ty, callee->getArg(0));
  auto *jmp_result = CB.CreateCall(jump_fn,
      {callee->getArg(0), target, callee->getArg(2)});
  CB.CreateRet(jmp_result);

  // Disconnected block: return.
  llvm::IRBuilder<> DB(disc);
  auto *ret_result = DB.CreateCall(ret_fn,
      {callee->getArg(0), callee->getArg(1), callee->getArg(2)});
  DB.CreateRet(ret_result);

  // Caller: calls callee, then uses result.
  auto *caller = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000", *M);
  auto *caller_entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> CBuilder(caller_entry);
  auto *call_result = CBuilder.CreateCall(callee,
      {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
  CBuilder.CreateRet(call_result);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // After inlining + neutralization, caller should not have
  // __remill_function_return calls in non-tail position.
  unsigned mid_returns = 0;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto *fn = CI->getCalledFunction();
        if (fn && fn->getName() == "__remill_function_return") {
          // Check if this is NOT in tail position.
          if (&BB.back() != CI) {
            auto *next = CI->getNextNode();
            if (!llvm::isa<llvm::ReturnInst>(next))
              ++mid_returns;
          }
        }
      }
    }
  }
  EXPECT_EQ(mid_returns, 0u)
      << "Inlined __remill_function_return calls should be neutralized";
}

// ===----------------------------------------------------------------------===
// Test 4: Empty module → no-op
// ===----------------------------------------------------------------------===

TEST_F(InlineJumpTargetsTest, EmptyModule_NoOp) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  runPass(*M);
  // Should not crash.
}

// ===----------------------------------------------------------------------===
// Test 5: Function with only constant-target jump → not lowered
// ===----------------------------------------------------------------------===

TEST_F(InlineJumpTargetsTest, ConstantJump_NotLowered) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *jump_fn = createRemillJump(*M);

  auto *F = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  // Constant-target jump → should NOT be lowered by this pass.
  auto *result = B.CreateCall(jump_fn,
      {F->getArg(0), llvm::ConstantInt::get(i64_ty, 0x180001010),
       F->getArg(2)});
  B.CreateRet(result);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Should still be a call, not a switch.
  auto *term = F->getEntryBlock().getTerminator();
  EXPECT_TRUE(llvm::isa<llvm::ReturnInst>(term))
      << "Constant-target jump should be left for Phase 3";
}

// ===----------------------------------------------------------------------===
// Test 6: Function without __remill_jump → no changes
// ===----------------------------------------------------------------------===

TEST_F(InlineJumpTargetsTest, NoJumps_NoChanges) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);

  auto *F = llvm::Function::Create(
      liftedFnTy(), llvm::Function::ExternalLinkage, "sub_180001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(2));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // Should still be a simple ret.
  EXPECT_TRUE(llvm::isa<llvm::ReturnInst>(F->getEntryBlock().getTerminator()));
}

}  // namespace
