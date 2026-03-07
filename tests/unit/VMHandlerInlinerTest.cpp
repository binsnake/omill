#include "omill/Passes/VMHandlerInliner.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <cstdlib>
#include <string>

#include <gtest/gtest.h>

namespace {

class VMHandlerInlinerTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  class ScopedEnvVar {
   public:
    ScopedEnvVar(const char *name, const char *value) : name_(name) {
      const char *old = std::getenv(name_.c_str());
      had_old_ = (old != nullptr);
      if (had_old_)
        old_ = old;
      set(value);
    }

    ~ScopedEnvVar() {
      if (had_old_)
        set(old_.c_str());
      else
        unset();
    }

   private:
    void set(const char *value) {
#if defined(_WIN32)
      _putenv_s(name_.c_str(), value ? value : "");
#else
      if (value)
        setenv(name_.c_str(), value, 1);
      else
        unsetenv(name_.c_str());
#endif
    }

    void unset() {
#if defined(_WIN32)
      _putenv_s(name_.c_str(), "");
#else
      unsetenv(name_.c_str());
#endif
    }

    std::string name_;
    bool had_old_ = false;
    std::string old_;
  };

  void runPass(llvm::Module &M, unsigned max_instrs = 200,
               unsigned min_callsites = 2) {
    llvm::ModulePassManager MPM;
    MPM.addPass(omill::VMHandlerInlinerPass(max_instrs, min_callsites));
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

  /// Create a small "handler" function: takes (ptr, i64) returns i64.
  llvm::Function *createHandler(llvm::Module &M, const char *name,
                                uint64_t addend) {
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
    auto *F = llvm::Function::Create(fn_ty, llvm::Function::InternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);

    // handler body: load from ptr, add constant, return.
    auto *val = B.CreateLoad(i64_ty, F->getArg(0));
    auto *result = B.CreateAdd(val, B.getInt64(addend));
    B.CreateRet(result);
    return F;
  }

  /// Create a lifted function (sub_*) that calls handlers.
  llvm::Function *createLiftedCaller(
      llvm::Module &M, const char *name,
      llvm::ArrayRef<llvm::Function *> handlers) {
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty}, false);
    auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);

    llvm::Value *acc = B.getInt64(0);
    for (auto *handler : handlers) {
      auto *result = B.CreateCall(handler, {F->getArg(0), acc});
      acc = result;
    }
    B.CreateRet(acc);
    return F;
  }
};

// ===----------------------------------------------------------------------===
// Test 1: Handlers called from 2+ lifted functions are inlined
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, HandlerInlinedWhenCallsitesExceedThreshold) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *h1 = createHandler(*M, "vm_add", 1);
  auto *h2 = createHandler(*M, "vm_sub", 2);

  // Two lifted functions both calling h1 and h2 → 2+ callsites each.
  createLiftedCaller(*M, "sub_401000", {h1, h2});
  createLiftedCaller(*M, "sub_402000", {h1, h2});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Before: handlers exist as separate functions.
  EXPECT_NE(M->getFunction("vm_add"), nullptr);
  EXPECT_NE(M->getFunction("vm_sub"), nullptr);

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // After: handlers should have been inlined.  They may still exist
  // (if not all callsites were inlineable) but calls should be gone.
  // Check that the lifted functions no longer call the handlers.
  auto *caller1 = M->getFunction("sub_401000");
  ASSERT_NE(caller1, nullptr);
  bool has_handler_call = false;
  for (auto &BB : *caller1) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee &&
            (callee->getName() == "vm_add" || callee->getName() == "vm_sub"))
          has_handler_call = true;
      }
    }
  }
  EXPECT_FALSE(has_handler_call);
}

// ===----------------------------------------------------------------------===
// Test 2: Handler with only 1 callsite is NOT inlined
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, SingleCallsiteHandler_NotInlined) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *h1 = createHandler(*M, "vm_single", 42);

  // Only one caller → only 1 callsite.
  createLiftedCaller(*M, "sub_401000", {h1});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Handler should still exist as a called function.
  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_handler_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "vm_single")
          has_handler_call = true;
      }
    }
  }
  EXPECT_TRUE(has_handler_call);
}

// ===----------------------------------------------------------------------===
// Test 3: Large handler exceeding threshold is NOT inlined
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, LargeHandler_NotInlined) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);

  // Create a large handler (many instructions).
  auto *big = llvm::Function::Create(fn_ty, llvm::Function::InternalLinkage,
                                     "vm_big", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", big);
  llvm::IRBuilder<> B(entry);
  llvm::Value *acc = big->getArg(1);
  for (int i = 0; i < 50; ++i) {
    acc = B.CreateAdd(acc, B.getInt64(i));
    acc = B.CreateMul(acc, B.getInt64(i + 1));
  }
  B.CreateRet(acc);

  createLiftedCaller(*M, "sub_401000", {big});
  createLiftedCaller(*M, "sub_402000", {big});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Use a very low threshold (5 instructions) → big handler won't qualify.
  runPass(*M, /*max_instrs=*/5);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Handler should still be called.
  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_handler_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "vm_big")
          has_handler_call = true;
      }
    }
  }
  EXPECT_TRUE(has_handler_call);
}

// ===----------------------------------------------------------------------===
// Test 4: Lifted functions (sub_*) are NOT treated as handlers
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, LiftedFunction_NotConsideredHandler) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  // sub_helper looks like a handler by size/callsite count, but is
  // a lifted function — should not be inlined.
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *helper = llvm::Function::Create(
      fn_ty, llvm::Function::InternalLinkage, "sub_helper", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(helper->getArg(1));

  createLiftedCaller(*M, "sub_401000", {helper});
  createLiftedCaller(*M, "sub_402000", {helper});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // sub_helper should still be called (not inlined).
  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "sub_helper")
          has_call = true;
      }
    }
  }
  EXPECT_TRUE(has_call);
}

// ===----------------------------------------------------------------------===
// Test 5: Remill/omill intrinsics are NOT inlined
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, RemillIntrinsics_Skipped) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // Create a __remill_ function with a body.
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *remill_fn = llvm::Function::Create(
      fn_ty, llvm::Function::InternalLinkage, "__remill_helper", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", remill_fn);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(remill_fn->getArg(2));

  // Call from lifted function.
  auto *caller_ty = llvm::FunctionType::get(i64_ty, {ptr_ty}, false);
  auto *caller = llvm::Function::Create(
      caller_ty, llvm::Function::ExternalLinkage, "sub_401000", *M);
  auto *centry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> CB(centry);
  auto *null_ptr = llvm::Constant::getNullValue(ptr_ty);
  CB.CreateCall(remill_fn, {null_ptr, CB.getInt64(0), null_ptr});
  CB.CreateCall(remill_fn, {null_ptr, CB.getInt64(0), null_ptr});
  CB.CreateCall(remill_fn, {null_ptr, CB.getInt64(0), null_ptr});
  CB.CreateRet(CB.getInt64(0));

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M, 200, 1);  // min_callsites=1 to not filter by count

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // __remill_helper should still be called.
  bool has_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *call = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = call->getCalledFunction();
        if (callee && callee->getName() == "__remill_helper")
          has_call = true;
      }
    }
  }
  EXPECT_TRUE(has_call);
}

// ===----------------------------------------------------------------------===
// Test 6: Empty module → no-op
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, EmptyModule_NoOp) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  runPass(*M);
  // Should not crash.
}

// ===----------------------------------------------------------------------===
// Test 7: _native wrapper callers trigger handler detection
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, NativeWrapperCallsCountAsCallsites) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *h1 = createHandler(*M, "vm_op", 7);

  // One call from a sub_ function, one from a _native wrapper.
  createLiftedCaller(*M, "sub_401000", {h1});

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty}, false);
  auto *native = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_401000_native", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native);
  llvm::IRBuilder<> B(entry);
  auto *result = B.CreateCall(h1, {native->getArg(0), B.getInt64(0)});
  B.CreateRet(result);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  // Handler should have been inlined (2 callsites: sub_ + _native).
  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "vm_op")
          has_call = true;
      }
    }
  }
  EXPECT_FALSE(has_call);
}

// ===----------------------------------------------------------------------===
// Test 8: Declaration-only handlers are NOT inlined
// ===----------------------------------------------------------------------===

TEST_F(VMHandlerInlinerTest, DeclarationHandler_Skipped) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *fn_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);

  // External declaration — can't inline.
  auto *ext = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                     "external_handler", *M);
  (void)ext;

  createLiftedCaller(*M, "sub_401000", {ext});
  createLiftedCaller(*M, "sub_402000", {ext});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  runPass(*M);

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  // Should not crash; external_handler should still be called.
  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "external_handler")
          has_call = true;
      }
    }
  }
  EXPECT_TRUE(has_call);
}

TEST_F(VMHandlerInlinerTest, AlreadyAlwaysInlineHandler_StillInlined) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *h = createHandler(*M, "vm_preinlined", 9);
  h->addFnAttr(llvm::Attribute::AlwaysInline);

  createLiftedCaller(*M, "sub_401000", {h});
  createLiftedCaller(*M, "sub_402000", {h});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  runPass(*M);
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "vm_preinlined")
          has_call = true;
      }
    }
  }
  EXPECT_FALSE(has_call);
}

TEST_F(VMHandlerInlinerTest, TaggedSingleCallsiteHandler_Inlined) {
  ScopedEnvVar force_marker("OMILL_INLINE_DIAG_MARKERS", "1");
  ScopedEnvVar skip_marker("OMILL_SKIP_INLINE_DIAG_MARKERS", "0");

  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *h = createHandler(*M, "vm_tagged", 3);
  h->addFnAttr("omill.vm_handler");

  // Single callsite would normally fail threshold; vm_handler tag should win.
  createLiftedCaller(*M, "sub_401000", {h});

  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  runPass(*M, /*max_instrs=*/200, /*min_callsites=*/2);
  ASSERT_FALSE(llvm::verifyModule(*M, &llvm::errs()));

  auto *caller = M->getFunction("sub_401000");
  ASSERT_NE(caller, nullptr);
  bool has_call = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (callee && callee->getName() == "vm_tagged")
          has_call = true;
      }
    }
  }
  EXPECT_FALSE(has_call);
}

}  // namespace
