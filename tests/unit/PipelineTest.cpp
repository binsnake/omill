#include "omill/Omill.h"

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
#include <cstdlib>

#ifdef _WIN32
#include <stdlib.h>  // _putenv_s
#endif

namespace {

/// Windows x64 data layout.  LLVM passes (InstCombine, etc.) can
/// dereference Module::getDataLayout() and crash if it is empty.
static const char *kDataLayout =
    "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
    "f80:128-n8:16:32:64-S128";

class PipelineTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(kDataLayout);
    return M;
  }

  void runPipeline(llvm::Module &M, const omill::PipelineOptions &opts) {
    llvm::ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);
    runMPM(MPM, M);
  }

  /// Run a module pass manager with all required analyses registered.
  /// NOTE: declaration order matters — MAM must be destroyed first (it holds
  /// cross-references to FAM via FunctionAnalysisManagerModuleProxy).
  void runMPM(llvm::ModulePassManager &MPM, llvm::Module &M) {
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

    omill::registerAnalyses(FAM);
    omill::registerModuleAnalyses(MAM);

    MPM.run(M, MAM);
  }

  /// Minimal opts: only Phase 0 + SynthesizeFlags run, then stops.
  omill::PipelineOptions minimalOpts() {
    omill::PipelineOptions opts;
    opts.lower_intrinsics = false;
    opts.optimize_state = false;
    opts.lower_control_flow = false;
    opts.recover_abi = false;
    opts.run_cleanup_passes = false;
    opts.stop_after_state_optimization = true;
    return opts;
  }

  /// Remill lifted function type: (ptr, i64, ptr) -> ptr
  llvm::FunctionType *liftedFnTy() {
    auto *ptr = llvm::PointerType::get(Ctx, 0);
    auto *i64 = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr, {ptr, i64, ptr}, false);
  }

  /// Create a void function with a trivial body (entry: ret void).
  llvm::Function *createDefinedFunction(llvm::Module &M, llvm::StringRef name,
                                        llvm::GlobalValue::LinkageTypes linkage =
                                            llvm::GlobalValue::ExternalLinkage) {
    auto *fnTy = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
    auto *F = llvm::Function::Create(fnTy, linkage, name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    B.CreateRetVoid();
    return F;
  }

  /// Create a remill intrinsic with a switch body (the pattern that
  /// StripRemillIntrinsicBodies is designed to handle).
  llvm::Function *createRemillIntrinsicWithBody(llvm::Module &M,
                                                 llvm::StringRef name) {
    auto *fnTy = liftedFnTy();
    auto *F = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                     name, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    auto *defBB = llvm::BasicBlock::Create(Ctx, "default", F);

    llvm::IRBuilder<> B(entry);
    B.CreateSwitch(F->getArg(1), defBB, 0);

    B.SetInsertPoint(defBB);
    B.CreateUnreachable();
    return F;
  }

  /// Create a sub_ function that calls the given callee (keeps callee alive
  /// through GlobalDCE).
  llvm::Function *createCallerOf(llvm::Module &M, llvm::StringRef callerName,
                                 llvm::Function *callee) {
    auto *fnTy = callee->getFunctionType();
    auto *F = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                     callerName, M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    llvm::SmallVector<llvm::Value *, 4> args;
    for (auto &arg : F->args())
      args.push_back(&arg);
    auto *call = B.CreateCall(callee, args);
    if (fnTy->getReturnType()->isVoidTy())
      B.CreateRetVoid();
    else
      B.CreateRet(call);
    return F;
  }

  void setEnv(const char *name, const char *value) {
#ifdef _WIN32
    _putenv_s(name, value);
#else
    setenv(name, value, 1);
#endif
  }

  void unsetEnv(const char *name) {
#ifdef _WIN32
    _putenv_s(name, "");
#else
    unsetenv(name);
#endif
  }
};

// ===----------------------------------------------------------------------===
// StripRemillIntrinsicBodies
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, StripSyncHyperCallBody) {
  auto M = createModule();
  auto *intrinsic = createRemillIntrinsicWithBody(*M, "__remill_sync_hyper_call");
  ASSERT_FALSE(intrinsic->isDeclaration());

  // Create a sub_ caller so the intrinsic survives GlobalDCE.
  createCallerOf(*M, "sub_140001000", intrinsic);

  runPipeline(*M, minimalOpts());

  auto *F = M->getFunction("__remill_sync_hyper_call");
  ASSERT_NE(F, nullptr);
  EXPECT_TRUE(F->isDeclaration())
      << "StripRemillIntrinsicBodiesPass should have deleted the body";
}

TEST_F(PipelineTest, StripAsyncHyperCallBody) {
  auto M = createModule();
  auto *intrinsic =
      createRemillIntrinsicWithBody(*M, "__remill_async_hyper_call");
  ASSERT_FALSE(intrinsic->isDeclaration());

  createCallerOf(*M, "sub_140002000", intrinsic);

  runPipeline(*M, minimalOpts());

  auto *F = M->getFunction("__remill_async_hyper_call");
  ASSERT_NE(F, nullptr);
  EXPECT_TRUE(F->isDeclaration())
      << "StripRemillIntrinsicBodiesPass should have deleted the body";
}

TEST_F(PipelineTest, StripIntrinsicBodiesSkipsDeclarations) {
  auto M = createModule();
  auto *F = llvm::Function::Create(liftedFnTy(),
                                   llvm::GlobalValue::ExternalLinkage,
                                   "__remill_sync_hyper_call", *M);
  ASSERT_TRUE(F->isDeclaration());

  // Give it a use so GlobalDCE doesn't remove it.
  createCallerOf(*M, "sub_140001000", F);

  runPipeline(*M, minimalOpts());

  F = M->getFunction("__remill_sync_hyper_call");
  ASSERT_NE(F, nullptr);
  EXPECT_TRUE(F->isDeclaration());
}

// ===----------------------------------------------------------------------===
// InternalizeRemillSemantics — functions
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, InternalizeFunctionsKeepsLiftedAndRemill) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_140001000");
  createDefinedFunction(*M, "block_140001000");
  createDefinedFunction(*M, "__remill_read_memory_64");
  auto *helper = createDefinedFunction(*M, "helper_func");

  // Give helper_func a caller so GlobalDCE doesn't remove it.
  auto *sub = M->getFunction("sub_140001000");
  sub->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", sub);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(helper);
  B.CreateRetVoid();

  runPipeline(*M, minimalOpts());

  // sub_, block_, __remill_ keep external linkage.
  EXPECT_FALSE(M->getFunction("sub_140001000")->hasLocalLinkage());
  EXPECT_FALSE(M->getFunction("block_140001000")->hasLocalLinkage());
  EXPECT_FALSE(M->getFunction("__remill_read_memory_64")->hasLocalLinkage());

  // helper_func with a body should be internalized.
  auto *h = M->getFunction("helper_func");
  ASSERT_NE(h, nullptr);
  EXPECT_TRUE(h->hasLocalLinkage());
}

TEST_F(PipelineTest, InternalizeSkipsDeclarations) {
  auto M = createModule();
  // Declaration only — should NOT be internalized.
  auto *fnTy = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
  auto *decl = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                      "external_decl", *M);

  // Defined helper — should be internalized.
  auto *helper = createDefinedFunction(*M, "helper_with_body");

  // Both need a caller to survive GlobalDCE.
  auto *sub = createDefinedFunction(*M, "sub_140001000");
  sub->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", sub);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(decl);
  B.CreateCall(helper);
  B.CreateRetVoid();

  runPipeline(*M, minimalOpts());

  auto *declAfter = M->getFunction("external_decl");
  ASSERT_NE(declAfter, nullptr);
  EXPECT_FALSE(declAfter->hasLocalLinkage())
      << "Declarations should not be internalized";

  auto *defAfter = M->getFunction("helper_with_body");
  ASSERT_NE(defAfter, nullptr);
  EXPECT_TRUE(defAfter->hasLocalLinkage())
      << "Defined non-lifted functions should be internalized";
}

TEST_F(PipelineTest, InternalizeKeepsAlreadyInternal) {
  auto M = createModule();
  auto *F = createDefinedFunction(*M, "already_internal",
                                  llvm::GlobalValue::InternalLinkage);

  // Give it a caller.
  auto *sub = createDefinedFunction(*M, "sub_140001000");
  sub->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", sub);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(F);
  B.CreateRetVoid();

  runPipeline(*M, minimalOpts());

  auto *result = M->getFunction("already_internal");
  ASSERT_NE(result, nullptr);
  EXPECT_TRUE(result->hasLocalLinkage());
}

// ===----------------------------------------------------------------------===
// InternalizeRemillSemantics — globals
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, InternalizeGlobalsKeepsRemillMarkers) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // __remill_ global: keep external.
  auto *remillGV = new llvm::GlobalVariable(
      *M, i64Ty, false, llvm::GlobalValue::ExternalLinkage,
      llvm::ConstantInt::get(i64Ty, 0), "__remill_basic_block");

  // Non-remill global with initializer: internalize.
  auto *tableGV = new llvm::GlobalVariable(
      *M, i64Ty, false, llvm::GlobalValue::ExternalLinkage,
      llvm::ConstantInt::get(i64Ty, 42), "some_table");

  // Give both globals a use so GlobalDCE doesn't remove them.
  auto *sub = createDefinedFunction(*M, "sub_140001000");
  sub->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", sub);
  llvm::IRBuilder<> B(entry);
  B.CreateLoad(i64Ty, remillGV);
  B.CreateLoad(i64Ty, tableGV);
  B.CreateRetVoid();

  runPipeline(*M, minimalOpts());

  auto *rGV = M->getNamedGlobal("__remill_basic_block");
  ASSERT_NE(rGV, nullptr);
  EXPECT_FALSE(rGV->hasLocalLinkage());

  auto *tGV = M->getNamedGlobal("some_table");
  ASSERT_NE(tGV, nullptr);
  EXPECT_TRUE(tGV->hasLocalLinkage());
}

// ===----------------------------------------------------------------------===
// PipelineOptions gating
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, StopAfterStateOptimizationSmoke) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_140001000");

  omill::PipelineOptions opts = minimalOpts();
  // Phase 0 + SynthesizeFlags, then stops.
  runPipeline(*M, opts);
  SUCCEED();
}

TEST_F(PipelineTest, AllOptionsFalseOnlyPhase0Runs) {
  auto M = createModule();
  // With body → should be internalized by Phase 0.
  createDefinedFunction(*M, "semantics_func");

  runPipeline(*M, minimalOpts());

  // GlobalDCE may have removed it (internal + no callers), or it's internal.
  auto *F = M->getFunction("semantics_func");
  if (F) {
    EXPECT_TRUE(F->hasLocalLinkage());
  }
}

TEST_F(PipelineTest, DeobfuscateSmoke) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_140001000");

  omill::PipelineOptions opts = minimalOpts();
  opts.deobfuscate = true;
  // Smoke test with deobfuscate. stop_after_state_optimization prevents
  // later phases that need BinaryMemoryAnalysis.
  runPipeline(*M, opts);
  SUCCEED();
}

// ===----------------------------------------------------------------------===
// Pipeline smoke tests
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, DefaultOptionsEmptyModuleSmoke) {
  auto M = createModule();
  omill::PipelineOptions opts = minimalOpts();
  runPipeline(*M, opts);
  SUCCEED();
}

TEST_F(PipelineTest, DefaultOptionsWithSubFunctionSmoke) {
  auto M = createModule();
  auto *fnTy = liftedFnTy();
  auto *F = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                   "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  auto *alloca = B.CreateAlloca(llvm::Type::getInt64Ty(Ctx));
  B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 42),
                alloca);
  B.CreateRet(F->getArg(0));

  omill::PipelineOptions opts = minimalOpts();
  runPipeline(*M, opts);
  SUCCEED();
}

TEST_F(PipelineTest, LowerIntrinsicsPhaseRuns) {
  auto M = createModule();
  auto *fnTy = liftedFnTy();
  auto *F = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                   "sub_140001000", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);
  B.CreateRet(F->getArg(0));

  omill::PipelineOptions opts = minimalOpts();
  opts.lower_intrinsics = true;
  // Smoke test: Phase 1 runs without crash.
  runPipeline(*M, opts);
  SUCCEED();
}

// ===----------------------------------------------------------------------===
// Env var disabling
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, EnvVarDisablesSynthesizeFlags) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_140001000");

  setEnv("OMILL_SKIP_SYNTHESIZE_FLAGS", "1");
  runPipeline(*M, minimalOpts());
  unsetEnv("OMILL_SKIP_SYNTHESIZE_FLAGS");
  SUCCEED();
}

TEST_F(PipelineTest, EnvVarZeroDoesNotDisable) {
  // '0' is not a disable value — only '1', 't', 'T' are.
  auto M = createModule();
  createDefinedFunction(*M, "sub_140001000");

  setEnv("OMILL_SKIP_SYNTHESIZE_FLAGS", "0");
  // SynthesizeFlags runs (not disabled by '0'). Should not crash.
  runPipeline(*M, minimalOpts());
  unsetEnv("OMILL_SKIP_SYNTHESIZE_FLAGS");
  SUCCEED();
}

TEST_F(PipelineTest, EnvVarTrueDisablesPass) {
  // 't' and 'T' also disable.
  auto M = createModule();
  createDefinedFunction(*M, "sub_140001000");

  setEnv("OMILL_SKIP_SYNTHESIZE_FLAGS", "t");
  runPipeline(*M, minimalOpts());
  unsetEnv("OMILL_SKIP_SYNTHESIZE_FLAGS");
  SUCCEED();
}

// ===----------------------------------------------------------------------===
// FoldCallsToConstantReturn (through buildABIRecoveryPipeline)
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, FoldCallsToConstantReturn) {
  auto M = createModule();
  auto *i64Ty = llvm::Type::getInt64Ty(Ctx);

  // Create a function that returns a constant.
  auto *retConstTy = llvm::FunctionType::get(i64Ty, false);
  auto *constFn = llvm::Function::Create(
      retConstTy, llvm::GlobalValue::InternalLinkage, "returns_42", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", constFn);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(llvm::ConstantInt::get(i64Ty, 42));
  }

  // Create a caller that uses the return value.
  auto *callerTy = llvm::FunctionType::get(i64Ty, false);
  auto *caller = llvm::Function::Create(
      callerTy, llvm::GlobalValue::ExternalLinkage, "sub_caller", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *callResult = B.CreateCall(constFn);
    B.CreateRet(callResult);
  }

  // Disable ABI passes that need remill IR; keep FoldCallsToConstantReturn.
  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE", "1");
  setEnv("OMILL_SKIP_ABI_GLOBAL_DCE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::buildABIRecoveryPipeline(MPM);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_GLOBAL_DCE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  // After folding, the call to returns_42 should have been replaced.
  auto *callerAfter = M->getFunction("sub_caller");
  ASSERT_NE(callerAfter, nullptr);
  ASSERT_FALSE(callerAfter->isDeclaration());

  bool foundCallToConst = false;
  for (auto &BB : *callerAfter) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (CI->getCalledFunction() &&
            CI->getCalledFunction()->getName() == "returns_42") {
          foundCallToConst = true;
        }
      }
    }
  }
  EXPECT_FALSE(foundCallToConst)
      << "Call to returns_42 should have been folded to constant";
}

// ===----------------------------------------------------------------------===
// GlobalDCE removes dead internalized functions
// ===----------------------------------------------------------------------===

TEST_F(PipelineTest, GlobalDCERemovesDeadInternalized) {
  auto M = createModule();
  // Create a non-lifted function with no callers. Phase 0 internalizes it,
  // then GlobalDCE removes it.
  createDefinedFunction(*M, "dead_helper");

  runPipeline(*M, minimalOpts());

  // The function should be gone — internalized (no callers) + DCE.
  EXPECT_EQ(M->getFunction("dead_helper"), nullptr);
}

}  // namespace
