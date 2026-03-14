#include "omill/Omill.h"
#include "omill/Analysis/VirtualCalleeRegistry.h"

#include <llvm/Analysis/CGSCCPassManager.h>
#include <llvm/Analysis/LoopAnalysisManager.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/PassInstrumentation.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>
#include <cstdlib>
#include <string>
#include <utility>
#include <vector>

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

  std::vector<std::pair<std::string, std::string>> collectFunctionPassRuns(
      llvm::Module &M, const omill::PipelineOptions &opts) {
    llvm::PassInstrumentationCallbacks PIC;
    std::vector<std::pair<std::string, std::string>> runs;
    PIC.registerBeforeNonSkippedPassCallback([&](llvm::StringRef PassName,
                                                 llvm::Any IR) {
      if (const auto **F = llvm::any_cast<const llvm::Function *>(&IR)) {
        runs.emplace_back(PassName.str(), (*F)->getName().str());
      }
    });

    llvm::ModulePassManager MPM;
    omill::buildPipeline(MPM, opts);

    llvm::PassBuilder PB(nullptr, llvm::PipelineTuningOptions(),
                         std::nullopt, &PIC);
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
    return runs;
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
  // Use __omill_ prefix so Phase 0 Protect/Unprotect passes skip it
  // (they treat all non-prefixed functions as remill semantics).
  auto *helper = createDefinedFunction(*M, "__omill_helper_func");

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

  // Non-lifted helper should be internalized.
  auto *h = M->getFunction("__omill_helper_func");
  ASSERT_NE(h, nullptr);
  EXPECT_TRUE(h->hasLocalLinkage());
}

TEST_F(PipelineTest, InternalizeSkipsDeclarations) {
  auto M = createModule();
  // Declaration only — should NOT be internalized.
  auto *fnTy = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
  auto *decl = llvm::Function::Create(fnTy, llvm::GlobalValue::ExternalLinkage,
                                      "external_decl", *M);

  // Defined helper — use __omill_ prefix so Phase 0 Protect/Unprotect
  // passes skip it (they treat all non-prefixed functions as remill
  // semantics and add alwaysinline, causing AlwaysInlinerPass to
  // inline and delete them before InternalizeRemillSemantics runs).
  auto *helper = createDefinedFunction(*M, "__omill_helper_with_body");

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

  auto *defAfter = M->getFunction("__omill_helper_with_body");
  ASSERT_NE(defAfter, nullptr);
  EXPECT_TRUE(defAfter->hasLocalLinkage())
      << "Defined non-lifted functions should be internalized";
}

TEST_F(PipelineTest, InternalizeKeepsAlreadyInternal) {
  auto M = createModule();
  // Use __omill_ prefix so Phase 0 Protect/Unprotect passes skip it.
  auto *F = createDefinedFunction(*M, "__omill_already_internal",
                                  llvm::GlobalValue::InternalLinkage);

  // Give it a caller.
  auto *sub = createDefinedFunction(*M, "sub_140001000");
  sub->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", sub);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(F);
  B.CreateRetVoid();

  runPipeline(*M, minimalOpts());

  auto *result = M->getFunction("__omill_already_internal");
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
  // Mark non-constant so the global can't be constant-folded away.
  auto *tableGV = new llvm::GlobalVariable(
      *M, i64Ty, false, llvm::GlobalValue::ExternalLinkage,
      llvm::ConstantInt::get(i64Ty, 42), "some_table");

  // Give both globals volatile uses so DCE/GlobalDCE can't remove them.
  auto *sub = createDefinedFunction(*M, "sub_140001000");
  sub->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", sub);
  llvm::IRBuilder<> B(entry);
  auto *ld1 = B.CreateLoad(i64Ty, remillGV, /*isVolatile=*/true);
  auto *ld2 = B.CreateLoad(i64Ty, tableGV, /*isVolatile=*/true);
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

TEST_F(PipelineTest, EarlyLiftPassesSkipProtectedSemanticHelpers) {
  auto M = createModule();
  auto *fnTy = liftedFnTy();

  auto *lifted = llvm::Function::Create(
      fnTy, llvm::GlobalValue::ExternalLinkage, "sub_140001000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(llvm::Type::getInt64Ty(Ctx));
    B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 7), slot);
    B.CreateRet(lifted->getArg(0));
  }

  auto *semantic = llvm::Function::Create(
      fnTy, llvm::GlobalValue::InternalLinkage, "semantic_helper", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", semantic);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(llvm::Type::getInt64Ty(Ctx));
    B.CreateStore(llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 9), slot);
    B.CreateRet(semantic->getArg(0));
  }

  omill::PipelineOptions opts = minimalOpts();
  opts.lower_intrinsics = true;
  opts.optimize_state = true;

  auto runs = collectFunctionPassRuns(*M, opts);

  auto sawRunOn = [&](llvm::StringRef pass_name, llvm::StringRef fn_name) {
    return llvm::any_of(runs, [&](const auto &run) {
      return run.first == pass_name && run.second == fn_name;
    });
  };

  EXPECT_TRUE(sawRunOn("LowerRemillIntrinsicsPass", "sub_140001000"));
  EXPECT_TRUE(sawRunOn("OptimizeStatePass", "sub_140001000"));
  EXPECT_FALSE(sawRunOn("LowerRemillIntrinsicsPass", "semantic_helper"));
  EXPECT_FALSE(sawRunOn("OptimizeStatePass", "semantic_helper"));
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
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
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

TEST_F(PipelineTest, AbiPipelineKeepsRegistryMarkedVirtualCalleeOutlined) {
  auto M = createModule();

  auto *wrapper = createDefinedFunction(*M, "sub_401100__vm_deadbeef_native");
  wrapper->addFnAttr("omill.vm_handler");

  std::vector<omill::VirtualCalleeRecord> records = {
      {"sub_401100__vm_deadbeef_native", "sub_401100_native", "caller_native",
       "hash_resolved", 0xDEADBEEFULL, 1, 0x500000ULL, 0xDEADBEEFULL, false},
  };
  omill::setVirtualCalleeRegistryMetadata(*M, records);

  auto *caller = createDefinedFunction(*M, "sub_caller_registry");
  caller->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(wrapper);
  B.CreateRetVoid();

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE", "1");
  setEnv("OMILL_SKIP_ABI_GLOBAL_DCE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_GLOBAL_DCE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  auto *callerAfter = M->getFunction("sub_caller_registry");
  ASSERT_NE(callerAfter, nullptr);
  bool stillCallsWrapper = false;
  for (auto &BB : *callerAfter) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == "sub_401100__vm_deadbeef_native")
          stillCallsWrapper = true;
      }
    }
  }
  EXPECT_TRUE(stillCallsWrapper);
}


TEST_F(PipelineTest, AbiPipelineKeepsDemergedWrapperOutlined) {
  auto M = createModule();

  auto *wrapper = createDefinedFunction(*M, "sub_401000__vm_abcdef_native");
  wrapper->addFnAttr("omill.vm_handler");
  wrapper->addFnAttr("omill.vm_demerged_clone", "1");
  wrapper->addFnAttr("omill.vm_outlined_virtual_call", "1");
  auto *caller = createDefinedFunction(*M, "sub_caller");
  caller->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(wrapper);
  B.CreateRetVoid();

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE", "1");
  setEnv("OMILL_SKIP_ABI_GLOBAL_DCE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_GLOBAL_DCE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  auto *callerAfter = M->getFunction("sub_caller");
  ASSERT_NE(callerAfter, nullptr);
  bool stillCallsWrapper = false;
  for (auto &BB : *callerAfter) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == "sub_401000__vm_abcdef_native")
          stillCallsWrapper = true;
      }
    }
  }
  EXPECT_TRUE(stillCallsWrapper);
}

TEST_F(PipelineTest, AbiPipelineInlinesClosedSliceNativeBlockHelpers) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *helper = createDefinedFunction(*M, "blk_401010_native");
  helper->addFnAttr("omill.closed_root_slice", "1");
  helper->addFnAttr(llvm::Attribute::NoInline);

  auto *root = createDefinedFunction(*M, "sub_401000_native");
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(helper);
    B.CreateRetVoid();
  }

  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");
  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_helper = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == "blk_401010_native")
          still_calls_helper = true;
      }
    }
  }
  EXPECT_FALSE(still_calls_helper);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
}

TEST_F(PipelineTest,
       AbiPipelineInlinesSingleUseLargeClosedSliceNativeBlockHelpers) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *helper = createDefinedFunction(*M, "blk_401020_native");
  helper->addFnAttr("omill.closed_root_slice", "1");
  helper->addFnAttr(llvm::Attribute::NoInline);
  helper->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(llvm::Type::getInt64Ty(Ctx));
    llvm::Value *acc = B.getInt64(0);
    for (unsigned i = 0; i < 128; ++i) {
      acc = B.CreateAdd(acc, B.getInt64(i + 1));
    }
    B.CreateStore(acc, slot);
    B.CreateRetVoid();
  }

  auto *root = createDefinedFunction(*M, "sub_401000_native");
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(helper);
    B.CreateRetVoid();
  }

  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");
  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_helper = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == "blk_401020_native")
          still_calls_helper = true;
      }
    }
  }
  EXPECT_FALSE(still_calls_helper);
  EXPECT_EQ(M->getFunction("blk_401020_native"), nullptr);
}

TEST_F(PipelineTest,
       AbiPipelineRemovesClosedSliceNativeBlockChainAndPreservesRootAttrs) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *leaf = createDefinedFunction(*M, "blk_401030_native");
  leaf->addFnAttr("omill.closed_root_slice", "1");
  leaf->addFnAttr(llvm::Attribute::NoInline);

  auto *mid = createDefinedFunction(*M, "blk_401020_native");
  mid->addFnAttr("omill.closed_root_slice", "1");
  mid->addFnAttr(llvm::Attribute::NoInline);
  mid->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(leaf);
    B.CreateRetVoid();
  }

  auto *head = createDefinedFunction(*M, "blk_401010_native");
  head->addFnAttr("omill.closed_root_slice", "1");
  head->addFnAttr(llvm::Attribute::NoInline);
  head->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", head);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(mid);
    B.CreateRetVoid();
  }

  auto *root = createDefinedFunction(*M, "sub_401000_native");
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(head);
    B.CreateRetVoid();
  }

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_GLOBAL_DCE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  EXPECT_TRUE(root_after->hasFnAttribute("omill.closed_root_slice"));
  EXPECT_TRUE(root_after->hasFnAttribute("omill.closed_root_slice_root"));
  EXPECT_NE(M->getModuleFlag("omill.closed_root_slice_scope"), nullptr);

  bool still_calls_blk = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName().starts_with("blk_"))
        still_calls_blk = true;
    }
  }
  EXPECT_FALSE(still_calls_blk);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
  EXPECT_EQ(M->getFunction("blk_401020_native"), nullptr);
  EXPECT_EQ(M->getFunction("blk_401030_native"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineCollapsesNullMemoryBlockContinuationCalls) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_401005", *M);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x401005ULL),
         llvm::ConstantPointerNull::get(ptr_ty)});
    B.CreateRet(call);
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE", "1");
  setEnv("OMILL_SKIP_ABI_SROA", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");
  setEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS", "1");
  setEnv("OMILL_SKIP_POST_ABI_INLINE", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_DEAD_STATE_STORE_DSE");
  unsetEnv("OMILL_SKIP_ABI_SROA");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_continuation = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "blk_401005")
        still_calls_continuation = true;
    }
  }
  EXPECT_FALSE(still_calls_continuation);
  EXPECT_EQ(M->getFunction("blk_401005"), nullptr);
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

TEST_F(PipelineTest, CleanupProfilesSmokeTest) {
  const omill::CleanupProfile profiles[] = {
      omill::CleanupProfile::kLightScalar,
      omill::CleanupProfile::kLightScalarNoInstCombine,
      omill::CleanupProfile::kStateToSSA,
      omill::CleanupProfile::kPostInline,
      omill::CleanupProfile::kBoundary,
      omill::CleanupProfile::kFinal,
  };

  for (auto profile : profiles) {
    auto M = createModule();
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *fn_ty =
        llvm::FunctionType::get(ptr_ty, {ptr_ty, llvm::Type::getInt64Ty(Ctx), ptr_ty},
                                false);
    auto *F = llvm::Function::Create(
        fn_ty, llvm::GlobalValue::ExternalLinkage, "sub_140001000", *M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *tmp = B.CreateAdd(B.getInt64(1), B.getInt64(2));
    auto *stack = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 8192),
                                 nullptr, "native_stack");
    auto *slot = B.CreateConstGEP1_64(B.getInt8Ty(), stack, 16);
    B.CreateStore(tmp, slot);
    auto *loaded = B.CreateLoad(B.getInt64Ty(), slot);
    B.CreateStore(loaded, B.CreateConstGEP1_64(B.getInt8Ty(), F->getArg(0), 0));
    B.CreateRet(F->getArg(2));

    llvm::ModulePassManager MPM;
    omill::buildCleanupPipeline(MPM, profile);
    runMPM(MPM, *M);
    EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
  }
}

TEST_F(PipelineTest, PostPatchCleanupPipelineSmokeTest) {
  auto M = createModule();
  auto *helper = createDefinedFunction(*M, "helper",
                                       llvm::GlobalValue::InternalLinkage);
  auto *caller = createDefinedFunction(*M, "sub_140001000");
  caller->deleteBody();
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  B.CreateCall(helper);
  B.CreateRetVoid();

  llvm::ModulePassManager MPM;
  omill::buildPostPatchCleanupPipeline(MPM, 20);
  runMPM(MPM, *M);

  EXPECT_FALSE(llvm::verifyModule(*M, &llvm::errs()));
}

TEST_F(PipelineTest, GenericStaticDevirtualizationMaterializesKnownEdge) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180005100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *caller = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_180005000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, caller->getArg(0), B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x180005100ULL), slot);
    auto *loaded = B.CreateLoad(i64_ty, slot);
    auto *call =
        B.CreateCall(dispatch, {caller->getArg(0), loaded, caller->getArg(2)});
    B.CreateRet(call);
  }

  omill::PipelineOptions opts;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.recover_abi = false;
  opts.deobfuscate = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(PipelineTest,
       ClosedSliceNoAbiCleanupCollapsesSingleUseBlkMustTailFallback) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *missing_block = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__remill_missing_block", *M);

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_401010", *M);
  helper->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *tail =
        B.CreateCall(missing_block, {helper->getArg(0), helper->getArg(1),
                                     helper->getArg(2)});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  omill::PipelineOptions opts;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.recover_abi = false;
  opts.deobfuscate = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  auto *root_after = M->getFunction("sub_401000");
  ASSERT_NE(root_after, nullptr);

  unsigned calls_helper = 0;
  unsigned calls_missing_block = 0;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "blk_401010")
        ++calls_helper;
      if (callee->getName() == "__remill_missing_block")
        ++calls_missing_block;
    }
  }

  EXPECT_EQ(calls_helper, 0u);
  EXPECT_GE(calls_missing_block, 1u);
  EXPECT_EQ(M->getFunction("blk_401010"), nullptr);
}

TEST_F(PipelineTest,
       ClosedSliceNoAbiCleanupKeepsBlkMustTailFallbackWhenDispatchLives) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__omill_dispatch_call", *M);
  auto *blk_decl = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_401030", *M);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *dispatched = B.CreateCall(
        dispatch, {root->getArg(0), B.getInt64(0x500000ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        blk_decl, {root->getArg(0), B.getInt64(0x401030ULL), dispatched});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  omill::PipelineOptions opts;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.recover_abi = false;
  opts.deobfuscate = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  auto *root_after = M->getFunction("sub_401000");
  ASSERT_NE(root_after, nullptr);

  unsigned calls_blk = 0;
  unsigned calls_missing_block = 0;
  unsigned calls_dispatch = 0;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "blk_401030")
        ++calls_blk;
      if (callee->getName() == "__remill_missing_block")
        ++calls_missing_block;
      if (callee->getName() == "__omill_dispatch_call")
        ++calls_dispatch;
    }
  }

  EXPECT_GE(calls_dispatch, 1u);
  EXPECT_GE(calls_blk, 1u);
  EXPECT_EQ(calls_missing_block, 0u);
}

TEST_F(PipelineTest,
       ClosedSliceNoAbiCleanupRewritesConstantMissingBlockCallToBlkTarget) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *missing_block = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__remill_missing_block", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_401030", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        missing_block, {root->getArg(0), B.getInt64(0x401030ULL), root->getArg(2)});
    B.CreateRet(call);
  }

  omill::PipelineOptions opts;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.recover_abi = false;
  opts.deobfuscate = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  auto *root_after = M->getFunction("sub_401000");
  ASSERT_NE(root_after, nullptr);

  unsigned calls_missing_block = 0;
  unsigned calls_blk = 0;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__remill_missing_block")
        ++calls_missing_block;
      if (callee->getName() == "blk_401030")
        ++calls_blk;
    }
  }

  EXPECT_EQ(calls_missing_block, 0u);
  EXPECT_GE(calls_blk, 1u);
}

}  // namespace
