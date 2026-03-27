#include "omill/Omill.h"
#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Passes/EliminateStateStruct.h"
#include "omill/Passes/LowerRemillIntrinsics.h"

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
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>

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

  std::vector<std::pair<std::string, std::string>> collectPassRuns(
      llvm::Module &M, const omill::PipelineOptions &opts) {
    llvm::PassInstrumentationCallbacks PIC;
    std::vector<std::pair<std::string, std::string>> runs;
    PIC.registerBeforeNonSkippedPassCallback([&](llvm::StringRef PassName,
                                                 llvm::Any IR) {
      if (const auto **Mod = llvm::any_cast<const llvm::Module *>(&IR)) {
        runs.emplace_back(PassName.str(), (*Mod)->getName().str());
      } else if (const auto **F = llvm::any_cast<const llvm::Function *>(&IR)) {
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

  void runMPM(llvm::ModulePassManager &MPM, llvm::Module &M,
              omill::BinaryMemoryMap map) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    MAM.registerPass(
        [&]() { return omill::BinaryMemoryAnalysis(std::move(map)); });
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

TEST_F(PipelineTest, AbiPipelineInlinesClosedSliceNativeSubHelpers) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *helper = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401010_native",
      *M);
  helper->addFnAttr("omill.closed_root_slice", "1");
  helper->addFnAttr(llvm::Attribute::NoInline);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64),
                                nullptr, "state_bytes");
    auto *base = B.CreateConstGEP1_64(B.getInt8Ty(), slot, 0);
    auto *as_i64 = B.CreatePtrToInt(base, B.getInt64Ty());
    auto *mixed = B.CreateXor(as_i64, B.getInt64(0x55));
    B.CreateRet(B.CreateIntToPtr(mixed, llvm::PointerType::get(Ctx, 0)));
  }

  auto *root = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401000_native",
      *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64),
                                 nullptr, "state_bytes");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    auto *call = B.CreateCall(root->getFunctionType(), helper,
                              {state_ptr, B.getInt64(0), state_ptr});
    B.CreateRet(call);
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
        if (callee && callee->getName() == "sub_401010_native")
          still_calls_helper = true;
      }
    }
  }
  EXPECT_FALSE(still_calls_helper);
  EXPECT_EQ(M->getFunction("sub_401010_native"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineInlinesClosedSliceSemanticHelpersAndRelowersMemory) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_mem = llvm::cast<llvm::Function>(
      M->getOrInsertFunction("__remill_read_memory_64", read_ty).getCallee());

  auto *helper_ty =
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {ptr_ty, ptr_ty},
                              false);
  auto *helper = llvm::Function::Create(
      helper_ty, llvm::GlobalValue::InternalLinkage, "semantic_helper", *M);
  helper->setMetadata("remill.function.type", llvm::MDNode::get(Ctx, {}));
  helper->addFnAttr(llvm::Attribute::NoInline);
  helper->addFnAttr(llvm::Attribute::OptimizeNone);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded = B.CreateCall(read_mem, {helper->getArg(0), B.getInt64(16)});
    auto *result = B.CreateAdd(loaded, B.getInt64(1));
    B.CreateStore(result, helper->getArg(1));
    B.CreateRetVoid();
  }

  auto *root_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(i64_ty, nullptr, "slot");
    auto *memory_ptr = B.CreateIntToPtr(root->getArg(0), ptr_ty, "memory");
    B.CreateCall(helper, {memory_ptr, slot});
    auto *loaded = B.CreateLoad(i64_ty, slot);
    B.CreateRet(loaded);
  }

  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");
  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_helper = false;
  bool still_calls_read_mem = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "semantic_helper")
        still_calls_helper = true;
      if (callee->getName() == "__remill_read_memory_64")
        still_calls_read_mem = true;
    }
  }

  EXPECT_FALSE(still_calls_helper);
  EXPECT_FALSE(still_calls_read_mem);
  EXPECT_EQ(M->getFunction("semantic_helper"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineInlinesSemanticHelpersEvenWithNonSliceCallers) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_mem = llvm::cast<llvm::Function>(
      M->getOrInsertFunction("__remill_read_memory_64", read_ty).getCallee());

  auto *helper_ty =
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {ptr_ty, ptr_ty},
                              false);
  auto *helper = llvm::Function::Create(
      helper_ty, llvm::GlobalValue::InternalLinkage, "semantic_helper", *M);
  helper->setMetadata("remill.function.type", llvm::MDNode::get(Ctx, {}));
  helper->addFnAttr(llvm::Attribute::NoInline);
  helper->addFnAttr(llvm::Attribute::OptimizeNone);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded = B.CreateCall(read_mem, {helper->getArg(0), B.getInt64(24)});
    B.CreateStore(loaded, helper->getArg(1));
    B.CreateRetVoid();
  }

  auto *other = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "other_user", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", other);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(i64_ty, nullptr, "slot");
    B.CreateCall(helper, {other->getArg(0), slot});
    B.CreateRetVoid();
  }

  auto *root_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(i64_ty, nullptr, "slot");
    auto *memory_ptr = B.CreateIntToPtr(root->getArg(0), ptr_ty, "memory");
    B.CreateCall(helper, {memory_ptr, slot});
    auto *loaded = B.CreateLoad(i64_ty, slot);
    B.CreateRet(loaded);
  }

  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");
  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_helper = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "semantic_helper")
        still_calls_helper = true;
    }
  }

  EXPECT_FALSE(still_calls_helper);
  EXPECT_EQ(M->getFunction("semantic_helper"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineRemovesDeadClosedSliceNativeSubHelpers) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *helper = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401010_native",
      *M);
  helper->addFnAttr("omill.closed_root_slice", "1");
  helper->addFnAttr(llvm::Attribute::NoInline);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 4096),
                                nullptr, "state_bytes");
    auto *base = B.CreateConstGEP1_64(B.getInt8Ty(), slot, 0);
    llvm::Value *acc = B.CreatePtrToInt(base, B.getInt64Ty());
    for (unsigned i = 0; i < 160; ++i) {
      acc = B.CreateAdd(acc, B.getInt64(i + 1));
    }
    B.CreateRet(B.CreateIntToPtr(acc, llvm::PointerType::get(Ctx, 0)));
  }

  auto *root = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401000_native",
      *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(root->getArg(2));
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

  EXPECT_NE(M->getFunction("sub_401000_native"), nullptr);
  EXPECT_EQ(M->getFunction("sub_401010_native"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineRemovesDeadNativeSubHelpersWithoutSliceAttrs) {
  auto M = createModule();

  auto *lifted_root = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  lifted_root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted_root);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted_root->getArg(2));
  }

  auto *helper = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401010_native",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 4096),
                                nullptr, "state_bytes");
    auto *base = B.CreateConstGEP1_64(B.getInt8Ty(), slot, 0);
    llvm::Value *acc = B.CreatePtrToInt(base, B.getInt64Ty());
    for (unsigned i = 0; i < 160; ++i) {
      acc = B.CreateAdd(acc, B.getInt64(i + 1));
    }
    B.CreateRet(B.CreateIntToPtr(acc, llvm::PointerType::get(Ctx, 0)));
  }

  auto *root = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401000_native",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(root->getArg(2));
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

  EXPECT_NE(M->getFunction("sub_401000_native"), nullptr);
  EXPECT_EQ(M->getFunction("sub_401010_native"), nullptr);
}

TEST_F(PipelineTest,
       AbiIntendedPrePipelineSkipsNoAbiOnlyClosedSliceRematerialization) {
  auto M = createModule();
  auto *lifted = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  omill::PipelineOptions opts;
  opts.recover_abi = false;  // main.cpp runs ABI later as a separate stage
  opts.no_abi_mode = false;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;
  opts.deobfuscate = false;
  opts.vm_devirtualize = false;

  auto runs = collectPassRuns(*M, opts);
  unsigned materialize_count = 0;
  unsigned late_closure_count = 0;
  unsigned lift_continuation_count = 0;
  unsigned lift_missing_block_count = 0;
  for (const auto &[pass_name, _] : runs) {
    if (pass_name.find("VirtualCFGMaterializationPass") != std::string::npos)
      ++materialize_count;
    if (pass_name.find("LateClosedRootSliceContinuationClosurePass") !=
        std::string::npos)
      ++late_closure_count;
    if (pass_name.find("LiftConstantContinuationDeclarationTargetsPass") !=
        std::string::npos)
      ++lift_continuation_count;
    if (pass_name.find("LiftConstantMissingBlockTargetsPass") !=
        std::string::npos)
      ++lift_missing_block_count;
  }

  EXPECT_EQ(materialize_count, 1u);
  EXPECT_EQ(late_closure_count, 0u);
  EXPECT_EQ(lift_continuation_count, 1u);
  EXPECT_EQ(lift_missing_block_count, 1u);
}

TEST_F(PipelineTest,
       ScopedLateRerunCanSkipClosedSliceMissingBlockLiftPass) {
  auto M = createModule();
  auto *lifted = llvm::Function::Create(
      liftedFnTy(), llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.no_abi_mode = false;
  opts.generic_static_devirtualize = true;
  opts.skip_closed_slice_missing_block_lift = true;
  opts.run_cleanup_passes = false;
  opts.deobfuscate = false;
  opts.vm_devirtualize = false;

  auto runs = collectPassRuns(*M, opts);
  unsigned lift_continuation_count = 0;
  unsigned lift_missing_block_count = 0;
  for (const auto &[pass_name, _] : runs) {
    if (pass_name.find("LiftConstantContinuationDeclarationTargetsPass") !=
        std::string::npos)
      ++lift_continuation_count;
    if (pass_name.find("LiftConstantMissingBlockTargetsPass") !=
        std::string::npos)
      ++lift_missing_block_count;
  }

  EXPECT_EQ(lift_continuation_count, 1u);
  EXPECT_EQ(lift_missing_block_count, 0u);
}

TEST_F(PipelineTest,
       NoAbiPipelineRunsSafeClosedSliceContinuationLiftsByDefault) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *lifted = llvm::Function::Create(liftedFnTy(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  lifted->addFnAttr("omill.closed_root_slice", "1");
  lifted->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  unsetEnv("OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY");
  unsetEnv("OMILL_ENABLE_NOABI_CLOSED_SLICE_RELIFT");

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.no_abi_mode = true;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;
  opts.deobfuscate = false;
  opts.vm_devirtualize = false;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;

  auto runs = collectPassRuns(*M, opts);
  unsigned late_closure_count = 0;
  unsigned lift_continuation_count = 0;
  unsigned lift_missing_block_count = 0;
  unsigned materialize_count = 0;
  for (const auto &[pass_name, _] : runs) {
    if (pass_name.find("LateClosedRootSliceContinuationClosurePass") !=
        std::string::npos)
      ++late_closure_count;
    if (pass_name.find("LiftConstantContinuationDeclarationTargetsPass") !=
        std::string::npos)
      ++lift_continuation_count;
    if (pass_name.find("LiftConstantMissingBlockTargetsPass") !=
        std::string::npos)
      ++lift_missing_block_count;
    if (pass_name.find("VirtualCFGMaterializationPass") != std::string::npos)
      ++materialize_count;
  }

  EXPECT_EQ(late_closure_count, 0u);
  EXPECT_EQ(lift_continuation_count, 1u);
  EXPECT_EQ(lift_missing_block_count, 1u);
  EXPECT_EQ(materialize_count, 2u);
}

TEST_F(PipelineTest, NoAbiPipelineCanSkipPostCleanupMaterialization) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *lifted = llvm::Function::Create(liftedFnTy(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  lifted->addFnAttr("omill.closed_root_slice", "1");
  lifted->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  setEnv("OMILL_SKIP_NOABI_POST_CLEANUP_MATERIALIZATION", "1");

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.no_abi_mode = true;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;
  opts.deobfuscate = false;
  opts.vm_devirtualize = false;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;

  auto runs = collectPassRuns(*M, opts);

  unsetEnv("OMILL_SKIP_NOABI_POST_CLEANUP_MATERIALIZATION");

  unsigned materialize_count = 0;
  for (const auto &[pass_name, _] : runs) {
    if (pass_name.find("VirtualCFGMaterializationPass") != std::string::npos)
      ++materialize_count;
  }

  EXPECT_EQ(materialize_count, 1u);
}

TEST_F(PipelineTest, NoAbiPipelineEnablesExperimentalClosedSliceExpansionWhenRequested) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *lifted = llvm::Function::Create(liftedFnTy(),
                                        llvm::GlobalValue::ExternalLinkage,
                                        "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  lifted->addFnAttr("omill.closed_root_slice", "1");
  lifted->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  setEnv("OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY", "1");
  setEnv("OMILL_ENABLE_NOABI_CLOSED_SLICE_RELIFT", "1");

  omill::PipelineOptions opts;
  opts.recover_abi = false;
  opts.no_abi_mode = true;
  opts.generic_static_devirtualize = true;
  opts.run_cleanup_passes = false;
  opts.deobfuscate = false;
  opts.vm_devirtualize = false;
  opts.lower_intrinsics = false;
  opts.optimize_state = false;
  opts.lower_control_flow = false;
  opts.resolve_indirect_targets = false;
  opts.interprocedural_const_prop = false;

  auto runs = collectPassRuns(*M, opts);

  unsetEnv("OMILL_ENABLE_CLOSED_SLICE_CONTINUATION_DISCOVERY");
  unsetEnv("OMILL_ENABLE_NOABI_CLOSED_SLICE_RELIFT");

  unsigned late_closure_count = 0;
  unsigned lift_continuation_count = 0;
  unsigned lift_missing_block_count = 0;
  for (const auto &[pass_name, _] : runs) {
    if (pass_name.find("LateClosedRootSliceContinuationClosurePass") !=
        std::string::npos)
      ++late_closure_count;
    if (pass_name.find("LiftConstantContinuationDeclarationTargetsPass") !=
        std::string::npos)
      ++lift_continuation_count;
    if (pass_name.find("LiftConstantMissingBlockTargetsPass") !=
        std::string::npos)
      ++lift_missing_block_count;
  }

  EXPECT_EQ(late_closure_count, 1u);
  EXPECT_EQ(lift_continuation_count, 1u);
  EXPECT_EQ(lift_missing_block_count, 1u);
}

TEST_F(PipelineTest,
       ClosedRootOutputRootCollapsesIntoNativeWrapperAndLowersMemory) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = liftedFnTy();
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_mem = llvm::cast<llvm::Function>(
      M->getOrInsertFunction("__remill_read_memory_64", read_ty).getCallee());

  auto *lifted = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  lifted->addFnAttr("omill.closed_root_slice", "1");
  lifted->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    auto *loaded = B.CreateCall(read_mem, {lifted->getArg(2), B.getInt64(8)});
    auto *result = B.CreateXor(loaded, B.getInt64(1));
    B.CreateRet(B.CreateIntToPtr(result, ptr_ty));
  }

  auto *native_ty = llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
  auto *native = llvm::Function::Create(
      native_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  native->addFnAttr("omill.closed_root_slice", "1");
  native->addFnAttr("omill.closed_root_slice_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native);
    llvm::IRBuilder<> B(entry);
    auto *state_storage =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "state_storage");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state_storage, 0);
    auto *memory_ptr = B.CreateIntToPtr(native->getArg(0), ptr_ty, "memory");
    auto *lifted_result =
        B.CreateCall(lifted, {state_ptr, B.getInt64(0), memory_ptr});
    B.CreateRet(B.CreatePtrToInt(lifted_result, i64_ty));
  }

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::EliminateStateStructPass());
  MPM.addPass(llvm::AlwaysInlinerPass());
  {
    llvm::FunctionPassManager FPM;
    FPM.addPass(
        omill::LowerRemillIntrinsicsPass(omill::LowerCategories::Memory));
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
  }
  MPM.addPass(llvm::GlobalDCEPass());
  runMPM(MPM, *M);

  auto *native_after = M->getFunction("sub_401000_native");
  ASSERT_NE(native_after, nullptr);
  bool calls_lifted = false;
  bool calls_read_mem = false;
  for (auto &BB : *native_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "sub_401000")
        calls_lifted = true;
      if (callee->getName() == "__remill_read_memory_64")
        calls_read_mem = true;
    }
  }

  EXPECT_FALSE(calls_lifted);
  EXPECT_FALSE(calls_read_mem);
  EXPECT_EQ(M->getFunction("sub_401000"), nullptr);
}

TEST_F(PipelineTest,
       AbiCleanupDcesDeadInternalizedLiftedHelpersWithoutNativeWrappers) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = liftedFnTy();
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_mem = llvm::cast<llvm::Function>(
      M->getOrInsertFunction("__remill_read_memory_64", read_ty).getCallee());

  auto *dead_helper = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", dead_helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded = B.CreateCall(read_mem, {dead_helper->getArg(2),
                                           B.getInt64(0x40)});
    auto *result = B.CreateXor(loaded, B.getInt64(0x55));
    B.CreateRet(B.CreateIntToPtr(result, ptr_ty));
  }

  auto *lifted = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  auto *native_ty = llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
  auto *native = llvm::Function::Create(
      native_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(B.getInt64(0));
  }

  llvm::ModulePassManager MPM;
  MPM.addPass(omill::EliminateStateStructPass());
  MPM.addPass(llvm::GlobalDCEPass());
  runMPM(MPM, *M);

  EXPECT_EQ(M->getFunction("sub_402000"), nullptr);
  auto *read_after = M->getFunction("__remill_read_memory_64");
  if (read_after)
    EXPECT_TRUE(read_after->use_empty());
}

TEST_F(PipelineTest,
       LiftInfrastructureCleanupDcesDeadExternalLiftedHelpers) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = liftedFnTy();
  auto *read_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *read_mem = llvm::cast<llvm::Function>(
      M->getOrInsertFunction("__remill_read_memory_64", read_ty).getCallee());

  auto *dead_helper = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", dead_helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded = B.CreateCall(read_mem, {dead_helper->getArg(2),
                                           B.getInt64(0x18)});
    B.CreateRet(B.CreateIntToPtr(loaded, ptr_ty));
  }

  auto *root_native_ty =
      llvm::FunctionType::get(i64_ty, {i64_ty, i64_ty}, false);
  auto *root_native = llvm::Function::Create(
      root_native_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root_native);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(B.getInt64(0));
  }

  llvm::ModulePassManager MPM;
  omill::buildLiftInfrastructureCleanupPipeline(MPM);
  runMPM(MPM, *M);

  EXPECT_EQ(M->getFunction("sub_402000"), nullptr);
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
    for (unsigned i = 0; i < 640; ++i) {
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

TEST_F(PipelineTest, AbiPipelineRemovesOutputRootNativeBlockChain) {
  auto M = createModule();

  auto *leaf = createDefinedFunction(*M, "blk_401030_native");
  leaf->addFnAttr(llvm::Attribute::NoInline);

  auto *mid = createDefinedFunction(*M, "blk_401020_native");
  mid->addFnAttr(llvm::Attribute::NoInline);
  mid->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(leaf);
    B.CreateRetVoid();
  }

  auto *head = createDefinedFunction(*M, "blk_401010_native");
  head->addFnAttr(llvm::Attribute::NoInline);
  head->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", head);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(mid);
    B.CreateRetVoid();
  }

  auto *root = createDefinedFunction(*M, "sub_401000_native");
  root->addFnAttr("omill.output_root");
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

TEST_F(PipelineTest,
       AbiPipelineNeutralizesInlinedFunctionReturnsInOutputRootHelpers) {
  auto M = createModule();
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ret_intr_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                              false);
  auto *ret_intr = llvm::cast<llvm::Function>(
      M->getOrInsertFunction("__remill_function_return", ret_intr_ty)
          .getCallee());

  auto *helper = createDefinedFunction(*M, "blk_401010_native");
  helper->addFnAttr(llvm::Attribute::NoInline);
  helper->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = B.CreateAlloca(B.getInt8Ty());
    B.CreateCall(ret_intr,
                 {state, B.getInt64(0),
                  llvm::ConstantPointerNull::get(ptr_ty)});
    B.CreateRetVoid();
  }

  auto *root = createDefinedFunction(*M, "sub_401000_native");
  root->addFnAttr("omill.output_root");
  root->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(helper);
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

  bool has_return_intrinsic = false;
  for (auto &F : *M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (callee && callee->getName() == "__remill_function_return")
          has_return_intrinsic = true;
      }
    }
  }

  EXPECT_FALSE(has_return_intrinsic);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineLoopifiesSelfRecursiveNativeBlockHelper) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *helper_ty =
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {i64_ty, i64_ty},
                              false);
  auto *helper = llvm::Function::Create(
      helper_ty, llvm::GlobalValue::ExternalLinkage, "blk_401010_native", *M);
  helper->addFnAttr(llvm::Attribute::NoInline);
  {
    auto arg_it = helper->arg_begin();
    llvm::Argument *idx = &*arg_it++;
    idx->setName("idx");
    llvm::Argument *acc = &*arg_it++;
    acc->setName("acc");

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    auto *recurse = llvm::BasicBlock::Create(Ctx, "recurse", helper);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper);

    llvm::IRBuilder<> B(entry);
    auto *cmp = B.CreateICmpULT(idx, B.getInt64(4));
    B.CreateCondBr(cmp, recurse, exit);

    B.SetInsertPoint(recurse);
    auto *next_idx = B.CreateAdd(idx, B.getInt64(1));
    auto *next_acc = B.CreateAdd(acc, next_idx);
    B.CreateCall(helper, {next_idx, next_acc});
    B.CreateBr(exit);

    B.SetInsertPoint(exit);
    B.CreateRetVoid();
  }

  auto *root_ty =
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(helper, {B.getInt64(0), B.getInt64(0)});
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
  bool still_calls_blk = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "blk_401010_native")
        still_calls_blk = true;
    }
  }

  EXPECT_FALSE(still_calls_blk);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
}

TEST_F(PipelineTest,
       AbiPipelineLoopifiesTrapTerminatedSelfRecursiveNativeBlockHelper) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  auto *helper_ty =
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {i64_ty, i64_ty},
                              false);
  auto *helper = llvm::Function::Create(
      helper_ty, llvm::GlobalValue::ExternalLinkage, "blk_401010_native", *M);
  helper->addFnAttr(llvm::Attribute::NoInline);
  {
    auto arg_it = helper->arg_begin();
    llvm::Argument *idx = &*arg_it++;
    idx->setName("idx");
    llvm::Argument *acc = &*arg_it++;
    acc->setName("acc");

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    auto *recurse = llvm::BasicBlock::Create(Ctx, "recurse", helper);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper);

    llvm::IRBuilder<> B(entry);
    auto *cmp = B.CreateICmpULT(idx, B.getInt64(4));
    B.CreateCondBr(cmp, recurse, exit);

    B.SetInsertPoint(recurse);
    auto *next_idx = B.CreateAdd(idx, B.getInt64(1));
    auto *next_acc = B.CreateAdd(acc, next_idx);
    B.CreateCall(helper, {next_idx, next_acc});
    auto *trap_ty =
        llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
    auto *trap_asm = llvm::InlineAsm::get(trap_ty, "int3", "",
                                          /*hasSideEffects=*/true);
    B.CreateCall(trap_ty, trap_asm, {});
    B.CreateRetVoid();

    B.SetInsertPoint(exit);
    B.CreateRetVoid();
  }

  auto *root_ty =
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(helper, {B.getInt64(0), B.getInt64(0)});
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
  bool still_calls_blk = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "blk_401010_native")
        still_calls_blk = true;
    }
  }

  EXPECT_FALSE(still_calls_blk);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
}

TEST_F(PipelineTest,
       AbiPipelineCollapsesMultiSiteAggregateSelfRecursiveNativeBlockHelper) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ret_ty = llvm::StructType::get(i64_ty, i64_ty);
  auto *helper_ty = llvm::FunctionType::get(ret_ty, {i64_ty, i64_ty}, false);

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::GlobalValue::InternalLinkage, "blk_401010_native", *M);
  helper->addFnAttr(llvm::Attribute::NoInline);
  {
    auto arg_it = helper->arg_begin();
    llvm::Argument *idx = &*arg_it++;
    idx->setName("idx");
    llvm::Argument *acc = &*arg_it++;
    acc->setName("acc");

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    auto *dispatch = llvm::BasicBlock::Create(Ctx, "dispatch", helper);
    auto *recurse0 = llvm::BasicBlock::Create(Ctx, "recurse0", helper);
    auto *recurse1 = llvm::BasicBlock::Create(Ctx, "recurse1", helper);
    auto *recurse2 = llvm::BasicBlock::Create(Ctx, "recurse2", helper);
    auto *recurse3 = llvm::BasicBlock::Create(Ctx, "recurse3", helper);
    auto *base = llvm::BasicBlock::Create(Ctx, "base", helper);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper);

    llvm::IRBuilder<> B(entry);
    auto *cmp = B.CreateICmpULT(idx, B.getInt64(6));
    B.CreateCondBr(cmp, dispatch, base);

    B.SetInsertPoint(dispatch);
    auto *mode = B.CreateAnd(acc, B.getInt64(3));
    B.CreateSwitch(mode, recurse3, 3);
    auto *switch_inst = llvm::cast<llvm::SwitchInst>(dispatch->getTerminator());
    switch_inst->addCase(B.getInt64(0), recurse0);
    switch_inst->addCase(B.getInt64(1), recurse1);
    switch_inst->addCase(B.getInt64(2), recurse2);

    llvm::SmallVector<llvm::BasicBlock *, 4> recurse_blocks = {
        recurse0, recurse1, recurse2, recurse3};
    llvm::SmallVector<llvm::Value *, 4> recur_idxs;
    llvm::SmallVector<llvm::Value *, 4> recur_accs;
    recur_idxs.reserve(recurse_blocks.size());
    recur_accs.reserve(recurse_blocks.size());
    for (unsigned i = 0; i < recurse_blocks.size(); ++i) {
      B.SetInsertPoint(recurse_blocks[i]);
      auto *next_idx = B.CreateAdd(idx, B.getInt64(1));
      llvm::Value *next_acc = acc;
      for (unsigned j = 0; j < 10; ++j) {
        next_acc = B.CreateAdd(next_acc, B.getInt64((i + 1) * (j + 1)));
        next_acc = B.CreateXor(next_acc, B.getInt64((i + 3) * 17 + j));
      }
      auto *call = B.CreateCall(helper, {next_idx, next_acc});
      recur_idxs.push_back(B.CreateExtractValue(call, 0));
      recur_accs.push_back(B.CreateExtractValue(call, 1));
      B.CreateBr(exit);
    }

    B.SetInsertPoint(base);
    llvm::Value *base_idx = idx;
    llvm::Value *base_acc = acc;
    for (unsigned i = 0; i < 12; ++i) {
      base_idx = B.CreateAdd(base_idx, B.getInt64(i + 1));
      base_acc = B.CreateXor(base_acc, base_idx);
    }
    B.CreateBr(exit);

    B.SetInsertPoint(exit);
    auto *idx_phi = B.CreatePHI(i64_ty, 5);
    auto *acc_phi = B.CreatePHI(i64_ty, 5);
    idx_phi->addIncoming(base_idx, base);
    acc_phi->addIncoming(base_acc, base);
    for (unsigned i = 0; i < recurse_blocks.size(); ++i) {
      idx_phi->addIncoming(recur_idxs[i], recurse_blocks[i]);
      acc_phi->addIncoming(recur_accs[i], recurse_blocks[i]);
    }
    llvm::Value *result = llvm::PoisonValue::get(ret_ty);
    result = B.CreateInsertValue(result, idx_phi, 0);
    result = B.CreateInsertValue(result, acc_phi, 1);
    B.CreateRet(result);
  }

  auto *root_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(helper, {B.getInt64(0), root->getArg(0)});
    auto *value = B.CreateExtractValue(call, 1);
    B.CreateRet(value);
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
  bool still_calls_blk = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "blk_401010_native")
        still_calls_blk = true;
    }
  }

  EXPECT_FALSE(still_calls_blk);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
}

TEST_F(PipelineTest,
       AbiPipelineCanonicalizesMutualRecursiveNativeBlockHelperPair) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ret_ty = llvm::StructType::get(i64_ty, i64_ty);
  auto *helper_a_ty =
      llvm::FunctionType::get(ret_ty, {i64_ty, i64_ty}, false);
  auto *helper_b_ty =
      llvm::FunctionType::get(ret_ty, {i64_ty, i64_ty, i64_ty}, false);

  auto *helper_a = llvm::Function::Create(helper_a_ty,
                                          llvm::GlobalValue::InternalLinkage,
                                          "blk_401010_native", *M);
  auto *helper_b = llvm::Function::Create(helper_b_ty,
                                          llvm::GlobalValue::InternalLinkage,
                                          "blk_401020_native", *M);
  helper_a->addFnAttr(llvm::Attribute::NoInline);
  helper_b->addFnAttr(llvm::Attribute::NoInline);

  auto build_heavy_base = [&](llvm::IRBuilder<> &B, llvm::Value *seed,
                              unsigned rounds) {
    llvm::Value *acc = seed;
    for (unsigned i = 0; i < rounds; ++i) {
      acc = B.CreateAdd(acc, B.getInt64((i + 3) * 11));
      acc = B.CreateXor(acc, B.getInt64((i + 5) * 17));
    }
    return acc;
  };

  {
    auto *idx = helper_a->getArg(0);
    idx->setName("idx");
    auto *acc = helper_a->getArg(1);
    acc->setName("acc");

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper_a);
    auto *recurse = llvm::BasicBlock::Create(Ctx, "recurse", helper_a);
    auto *base = llvm::BasicBlock::Create(Ctx, "base", helper_a);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper_a);

    llvm::IRBuilder<> B(entry);
    auto *cond = B.CreateICmpULT(idx, B.getInt64(3));
    B.CreateCondBr(cond, recurse, base);

    B.SetInsertPoint(recurse);
    auto *next_idx = B.CreateAdd(idx, B.getInt64(1));
    auto *next_acc = build_heavy_base(B, acc, 80);
    auto *call = B.CreateCall(helper_b, {next_idx, next_acc, B.getInt64(7)});
    auto *recur0 = B.CreateExtractValue(call, 0);
    auto *recur1 = B.CreateExtractValue(call, 1);
    B.CreateBr(exit);

    B.SetInsertPoint(base);
    auto *base0 = build_heavy_base(B, idx, 60);
    auto *base1 = build_heavy_base(B, acc, 60);
    B.CreateBr(exit);

    B.SetInsertPoint(exit);
    auto *phi0 = B.CreatePHI(i64_ty, 2);
    auto *phi1 = B.CreatePHI(i64_ty, 2);
    phi0->addIncoming(recur0, recurse);
    phi0->addIncoming(base0, base);
    phi1->addIncoming(recur1, recurse);
    phi1->addIncoming(base1, base);
    llvm::Value *result = llvm::PoisonValue::get(ret_ty);
    result = B.CreateInsertValue(result, phi0, 0);
    result = B.CreateInsertValue(result, phi1, 1);
    B.CreateRet(result);
  }

  {
    auto *idx = helper_b->getArg(0);
    idx->setName("idx");
    auto *acc = helper_b->getArg(1);
    acc->setName("acc");
    auto *salt = helper_b->getArg(2);
    salt->setName("salt");

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper_b);
    auto *recurse = llvm::BasicBlock::Create(Ctx, "recurse", helper_b);
    auto *base = llvm::BasicBlock::Create(Ctx, "base", helper_b);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper_b);

    llvm::IRBuilder<> B(entry);
    auto *cond = B.CreateICmpULT(idx, B.getInt64(4));
    B.CreateCondBr(cond, recurse, base);

    B.SetInsertPoint(recurse);
    auto *next_idx = B.CreateAdd(idx, B.getInt64(1));
    auto *seed = B.CreateAdd(acc, salt);
    auto *next_acc = build_heavy_base(B, seed, 80);
    auto *call = B.CreateCall(helper_a, {next_idx, next_acc});
    auto *recur0 = B.CreateExtractValue(call, 0);
    auto *recur1 = B.CreateExtractValue(call, 1);
    B.CreateBr(exit);

    B.SetInsertPoint(base);
    auto *base0 = build_heavy_base(B, idx, 60);
    auto *base1 = build_heavy_base(B, seed, 60);
    B.CreateBr(exit);

    B.SetInsertPoint(exit);
    auto *phi0 = B.CreatePHI(i64_ty, 2);
    auto *phi1 = B.CreatePHI(i64_ty, 2);
    phi0->addIncoming(recur0, recurse);
    phi0->addIncoming(base0, base);
    phi1->addIncoming(recur1, recurse);
    phi1->addIncoming(base1, base);
    llvm::Value *result = llvm::PoisonValue::get(ret_ty);
    result = B.CreateInsertValue(result, phi0, 0);
    result = B.CreateInsertValue(result, phi1, 1);
    B.CreateRet(result);
  }

  auto *root_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    llvm::Value *sum = root->getArg(0);
    for (unsigned i = 0; i < 4; ++i) {
      auto *call_a =
          B.CreateCall(helper_a, {B.getInt64(i), B.CreateAdd(sum, B.getInt64(i))});
      sum = B.CreateAdd(sum, B.CreateExtractValue(call_a, 1));
      auto *call_b = B.CreateCall(
          helper_b, {B.getInt64(i + 1), sum, B.getInt64(9 + i)});
      sum = B.CreateXor(sum, B.CreateExtractValue(call_b, 0));
    }
    B.CreateRet(sum);
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

  bool still_calls_original_helpers = false;
  unsigned remaining_block_helper_defs = 0;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && (callee->getName() == "blk_401010_native" ||
                     callee->getName() == "blk_401020_native")) {
        still_calls_original_helpers = true;
      }
    }
  }

  for (auto &F : *M) {
    if (!F.isDeclaration() &&
        (F.getName().starts_with("blk_") || F.getName().starts_with("block_")) &&
        F.getName().ends_with("_native")) {
      ++remaining_block_helper_defs;
    }
  }

  EXPECT_FALSE(still_calls_original_helpers);
  EXPECT_EQ(M->getFunction("blk_401010_native"), nullptr);
  EXPECT_EQ(M->getFunction("blk_401020_native"), nullptr);
  EXPECT_EQ(remaining_block_helper_defs, 1u);
}

TEST_F(PipelineTest,
       AbiPipelineForceInlinesSingleCallerCommonContinuationNativeHelper) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *helper_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::GlobalValue::InternalLinkage, "blk_401030_native", *M);
  helper->addFnAttr(llvm::Attribute::NoInline);
  {
    auto *arg = helper->getArg(0);
    arg->setName("seed");

    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    llvm::Value *acc = arg;
    for (unsigned i = 0; i < 160; ++i) {
      acc = B.CreateAdd(acc, B.getInt64((i + 1) * 3));
      acc = B.CreateXor(acc, B.getInt64((i + 5) * 17));
    }
    B.CreateRet(acc);
  }

  auto *root_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
  auto *root = llvm::Function::Create(
      root_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *call0 = llvm::BasicBlock::Create(Ctx, "call0", root);
    auto *call1 = llvm::BasicBlock::Create(Ctx, "call1", root);
    auto *call2 = llvm::BasicBlock::Create(Ctx, "call2", root);
    auto *call3 = llvm::BasicBlock::Create(Ctx, "call3", root);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", root);

    llvm::IRBuilder<> B(entry);
    auto *selector = B.CreateAnd(root->getArg(0), B.getInt64(3));
    auto *sw = B.CreateSwitch(selector, call3, 3);
    sw->addCase(B.getInt64(0), call0);
    sw->addCase(B.getInt64(1), call1);
    sw->addCase(B.getInt64(2), call2);

    llvm::SmallVector<llvm::BasicBlock *, 4> call_blocks = {
        call0, call1, call2, call3};
    llvm::SmallVector<llvm::Value *, 4> call_results;
    for (unsigned i = 0; i < call_blocks.size(); ++i) {
      B.SetInsertPoint(call_blocks[i]);
      auto *arg = B.CreateAdd(root->getArg(0), B.getInt64(i * 11));
      auto *call = B.CreateCall(helper, {arg});
      call_results.push_back(call);
      B.CreateBr(exit);
    }

    B.SetInsertPoint(exit);
    auto *phi = B.CreatePHI(i64_ty, static_cast<unsigned>(call_blocks.size()));
    for (unsigned i = 0; i < call_blocks.size(); ++i)
      phi->addIncoming(call_results[i], call_blocks[i]);
    B.CreateRet(phi);
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
  bool still_calls_helper = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "blk_401030_native")
        still_calls_helper = true;
    }
  }

  EXPECT_FALSE(still_calls_helper);
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

TEST_F(PipelineTest,
       AbiPipelineTerminalizesPoisonMemoryBlockContinuationCalls) {
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
    auto *state_storage =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "state_storage");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state_storage, 0);
    B.CreateStore(B.getInt8(1), state_ptr);
    B.CreateCall(continuation,
                 {state_ptr, B.getInt64(0x401005ULL),
                  llvm::PoisonValue::get(ptr_ty)});
    B.CreateUnreachable();
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
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
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_continuation = false;
  bool calls_missing_block_handler = false;
  bool has_alloca = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::AllocaInst>(&I))
        has_alloca = true;
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "blk_401005")
        still_calls_continuation = true;
      if (callee->getName() == "__omill_missing_block_handler")
        calls_missing_block_handler = true;
    }
  }
  EXPECT_FALSE(still_calls_continuation);
  EXPECT_TRUE(calls_missing_block_handler);
  EXPECT_FALSE(has_alloca);
  EXPECT_EQ(M->getFunction("blk_401005"), nullptr);
}

TEST_F(
    PipelineTest,
    AbiPipelineTerminalizesSelfLoopPoisonMemoryBlockContinuationWithDeadPureSuffix) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_401005", *M);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  root->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop", root);
    llvm::IRBuilder<> B(entry);
    auto *state_storage =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "state_storage");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state_storage, 0);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateCall(continuation,
                  {state_ptr, LB.getInt64(0x401005ULL),
                   llvm::PoisonValue::get(ptr_ty)});
    auto *dead_add = LB.CreateAdd(root->getArg(1), LB.getInt64(1), "dead.add");
    (void)dead_add;
    LB.CreateBr(loop);
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
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
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_continuation = false;
  bool calls_missing_block_handler = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "blk_401005")
        still_calls_continuation = true;
      if (callee->getName() == "__omill_missing_block_handler")
        calls_missing_block_handler = true;
    }
  }
  EXPECT_FALSE(still_calls_continuation);
  EXPECT_TRUE(calls_missing_block_handler);
  EXPECT_EQ(M->getFunction("blk_401005"), nullptr);
}

TEST_F(PipelineTest, AbiPipelineErasesIsolatedSyntheticBlockWrapperCall) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_401005", *M);
  auto *lifetime_end = llvm::cast<llvm::Function>(
      llvm::Intrinsic::getOrInsertDeclaration(
          M.get(), llvm::Intrinsic::lifetime_end, {ptr_ty}));

  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr, "state");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    B.CreateCall(continuation,
                 {state_ptr, B.getInt64(0x401005ULL),
                  llvm::PoisonValue::get(ptr_ty)});
    B.CreateCall(lifetime_end, {B.getInt64(64), state_ptr});
    B.CreateRet(B.getInt64(0x1234));
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
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
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool still_calls_continuation = false;
  bool calls_missing_block_handler = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "blk_401005")
        still_calls_continuation = true;
      if (callee->getName() == "__omill_missing_block_handler")
        calls_missing_block_handler = true;
    }
  }
  EXPECT_FALSE(still_calls_continuation);
  EXPECT_FALSE(calls_missing_block_handler);
  EXPECT_EQ(M->getFunction("blk_401005"), nullptr);
}

TEST_F(PipelineTest,
       AbiPipelineAnnotatesTerminalMissingBlockHandlerClassification) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Warning, "omill.target_arch",
                   static_cast<uint32_t>(omill::TargetArch::kX86_64));

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "blk_401005", *M);

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state_storage =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "state_storage");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state_storage, 0);
    B.CreateCall(continuation,
                 {state_ptr, B.getInt64(0x401005ULL),
                  llvm::PoisonValue::get(ptr_ty)});
    B.CreateUnreachable();
  }

  omill::BinaryMemoryMap map;
  static const uint8_t bytes[16] = {};
  map.setImageBase(0x400000);
  map.setImageSize(0x2000);
  map.addRegion(0x401000, bytes, sizeof(bytes), /*read_only=*/false,
                /*executable=*/false);

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");
  setEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS", "1");
  setEnv("OMILL_SKIP_POST_ABI_INLINE", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M, std::move(map));

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_ALWAYS_INLINE");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  EXPECT_TRUE(root_after->hasFnAttribute("omill.terminal_boundary_count"));
  EXPECT_EQ(root_after->getFnAttribute("omill.terminal_boundary_count")
                .getValueAsString(),
            "1");
  EXPECT_EQ(root_after->getFnAttribute("omill.terminal_boundary_kind")
                .getValueAsString(),
            "in_image_non_executable_target");
  EXPECT_EQ(root_after->getFnAttribute("omill.terminal_boundary_target_va")
                .getValueAsString(),
            "401005");

  bool found_annotated_missing_handler = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee || callee->getName() != "__omill_missing_block_handler")
        continue;
      auto *md = CI->getMetadata("omill.terminal_boundary");
      ASSERT_NE(md, nullptr);
      ASSERT_GE(md->getNumOperands(), 4u);
      auto *kind_tag = llvm::dyn_cast<llvm::MDString>(md->getOperand(0));
      auto *kind_value = llvm::dyn_cast<llvm::MDString>(md->getOperand(1));
      ASSERT_NE(kind_tag, nullptr);
      ASSERT_NE(kind_value, nullptr);
      EXPECT_EQ(kind_tag->getString(), "kind");
      EXPECT_EQ(kind_value->getString(), "in_image_non_executable_target");
      found_annotated_missing_handler = true;
    }
  }
  EXPECT_TRUE(found_annotated_missing_handler);

  auto *named_md = M->getNamedMetadata("omill.terminal_boundaries");
  ASSERT_NE(named_md, nullptr);
  ASSERT_EQ(named_md->getNumOperands(), 1u);
}

TEST_F(PipelineTest, AbiPipelineRewritesLoopifiedTerminalBoundaryOutputRoot) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", root);
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    auto *br = LB.CreateBr(loop);
    br->setMetadata(
        "omill.loopified_terminal_pc",
        llvm::MDTuple::get(
            Ctx, {llvm::ConstantAsMetadata::get(
                      llvm::ConstantInt::get(i64_ty, 0x401005ULL))}));
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
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
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool found_missing_handler = false;
  bool found_self_loop = false;
  for (auto &BB : *root_after) {
    if (auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator())) {
      if (br->isUnconditional() && br->getSuccessor(0) == &BB)
        found_self_loop = true;
    }
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }
  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_self_loop);
}

TEST_F(PipelineTest,
       AbiPipelineRewritesLoopifiedTerminalBoundaryOutputRootFromAttrFallback) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.loopified_terminal_pc", "401005");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", root);
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateBr(loop);
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
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
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  bool found_missing_handler = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }
  EXPECT_TRUE(found_missing_handler);
  EXPECT_TRUE(root_after->hasFnAttribute("omill.terminal_boundary_kind"));
}

TEST_F(PipelineTest,
       AbiPipelinePropagatesTerminalBoundaryCandidateFromLiftedToNativeRoot) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *lifted = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  lifted->addFnAttr("omill.terminal_boundary_candidate_pc", "401005");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(lifted->getArg(2));
  }

  auto *native = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  native->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", native);
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateBr(loop);
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_ALWAYS_INLINE", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
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
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *native_after = M->getFunction("sub_401000_native");
  ASSERT_NE(native_after, nullptr);
  bool found_missing_handler = false;
  for (auto &BB : *native_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }
  EXPECT_TRUE(found_missing_handler);
  EXPECT_TRUE(native_after->hasFnAttribute("omill.terminal_boundary_kind"));
}

TEST_F(PipelineTest,
       AbiPipelinePropagatesTerminalBoundaryCandidateFromUniqueCalleeBeforeInlining) {
  auto M = createModule();

  auto *helper = createDefinedFunction(*M, "blk_401020_native");
  helper->addFnAttr(llvm::Attribute::AlwaysInline);
  helper->addFnAttr("omill.terminal_boundary_candidate_pc", "401005");
  helper->deleteBody();
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", helper);
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateBr(loop);
  }

  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(helper);
    B.CreateUnreachable();
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");
  setEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS", "1");
  setEnv("OMILL_SKIP_POST_ABI_INLINE", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);

  bool found_missing_handler = false;
  bool found_self_loop = false;
  for (auto &BB : *root_after) {
    if (BB.getName() == "selfrec.loop.i")
      found_self_loop = true;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }

  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_self_loop);
}

TEST_F(PipelineTest,
       AbiPipelinePropagatesLiftedTerminalBoundaryCandidateBeforeInlining) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *lifted = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  lifted->addFnAttr("omill.output_root");
  lifted->addFnAttr(llvm::Attribute::AlwaysInline);
  lifted->addFnAttr("omill.terminal_boundary_candidate_pc", "401005");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateBr(loop);
  }

  auto *native = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  native->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native);
    llvm::IRBuilder<> B(entry);
    auto *state_storage =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "state_storage");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state_storage, 0);
    auto *memory_ptr = B.CreateIntToPtr(native->getArg(0), ptr_ty, "memory");
    auto *lifted_result =
        B.CreateCall(lifted, {state_ptr, B.getInt64(0), memory_ptr});
    B.CreateRet(B.CreatePtrToInt(lifted_result, i64_ty));
  }

  setEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES", "1");
  setEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE", "1");
  setEnv("OMILL_SKIP_ABI_FINAL_OPT", "1");
  setEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS", "1");
  setEnv("OMILL_SKIP_POST_ABI_INLINE", "1");

  llvm::ModulePassManager MPM;
  omill::PipelineOptions opts;
  omill::buildABIRecoveryPipeline(MPM, opts);
  runMPM(MPM, *M);

  unsetEnv("OMILL_SKIP_ABI_RECOVER_SIGNATURES");
  unsetEnv("OMILL_SKIP_ABI_REWRITE_LIFTED_LATE");
  unsetEnv("OMILL_SKIP_ABI_FINAL_OPT");
  unsetEnv("OMILL_SKIP_ABI_INLINE_VM_HANDLERS");
  unsetEnv("OMILL_SKIP_POST_ABI_INLINE");

  auto *native_after = M->getFunction("sub_401000_native");
  ASSERT_NE(native_after, nullptr);

  bool found_missing_handler = false;
  bool found_self_loop = false;
  for (auto &BB : *native_after) {
    if (BB.getName() == "selfrec.loop.i")
      found_self_loop = true;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }

  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_self_loop);
}

TEST_F(PipelineTest,
       LateCleanupRewritesTerminalBoundaryOutputRootFromCandidateAttr) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.terminal_boundary_candidate_pc", "401005");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", root);
    llvm::IRBuilder<> B(entry);
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateBr(loop);
  }

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);

  bool found_missing_handler = false;
  bool found_self_loop = false;
  for (auto &BB : *root_after) {
    if (BB.getName() == "selfrec.loop.i")
      found_self_loop = true;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }

  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_self_loop);
}

TEST_F(PipelineTest,
       LateCleanupRewritesAllocaBackedSelfLoopTerminalBoundaryOutputRoot) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.terminal_boundary_candidate_pc", "401234");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", root);
    llvm::IRBuilder<> B(entry);
    auto *stack =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "native_stack");
    (void) stack;
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    LB.CreateLifetimeStart(stack, llvm::ConstantInt::get(i64_ty, 64));
    auto *addr = LB.CreateGEP(B.getInt8Ty(), stack, LB.getInt64(16));
    LB.CreateStore(LB.getInt64(0), LB.CreateIntToPtr(
                                      LB.CreatePtrToInt(addr, i64_ty), ptr_ty));
    LB.CreateLifetimeEnd(stack, llvm::ConstantInt::get(i64_ty, 64));
    LB.CreateBr(loop);
  }

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);

  bool found_missing_handler = false;
  bool found_self_loop = false;
  for (auto &BB : *root_after) {
    if (BB.getName() == "selfrec.loop.i")
      found_self_loop = true;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }

  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_self_loop);
}

TEST_F(PipelineTest,
       LateCleanupRewritesIndirectCallTerminalBoundaryOutputRoot) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *loop = llvm::BasicBlock::Create(Ctx, "selfrec.loop.i", root);
    llvm::IRBuilder<> B(entry);
    auto *slot =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 32), nullptr,
                       "state_bytes");
    B.CreateMemSet(slot, B.getInt8(0), 32, llvm::MaybeAlign(16));
    B.CreateBr(loop);

    llvm::IRBuilder<> LB(loop);
    auto *indirect_ty = llvm::FunctionType::get(i64_ty, {i64_ty}, false);
    auto *indirect_callee = llvm::ConstantExpr::getIntToPtr(
        llvm::ConstantInt::get(i64_ty, 0x401234ULL),
        llvm::PointerType::get(Ctx, 0));
    LB.CreateCall(indirect_ty, indirect_callee, {LB.getInt64(7)});
    LB.CreateBr(loop);
  }

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);

  bool found_missing_handler = false;
  bool found_self_loop = false;
  for (auto &BB : *root_after) {
    if (BB.getName() == "selfrec.loop.i")
      found_self_loop = true;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
    }
  }

  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_self_loop);
  EXPECT_TRUE(root_after->hasFnAttribute("omill.terminal_boundary_kind"));
  auto target_attr =
      root_after->getFnAttribute("omill.terminal_boundary_target_va");
  ASSERT_TRUE(target_attr.isValid());
  EXPECT_EQ(target_attr.getValueAsString(), "401234");
}

TEST_F(PipelineTest,
       LateCleanupRewritesStateWrapperTerminalBoundaryOutputRoot) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  state_ty->setBody(llvm::ArrayType::get(llvm::Type::getInt8Ty(Ctx), 64));

  auto *lifted = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), {ptr_ty, i64_ty},
                              false),
      llvm::GlobalValue::InternalLinkage, "sub_401000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", lifted);
    llvm::IRBuilder<> B(entry);
    B.CreateRetVoid();
  }

  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.terminal_boundary_candidate_pc", "401234");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = B.CreateAlloca(state_ty, nullptr, "state");
    auto *stack = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 32),
                                 nullptr, "stack");
    B.CreateMemSet(state, B.getInt8(0), 64, llvm::MaybeAlign(16));
    B.CreateMemSet(stack, B.getInt8(0), 32, llvm::MaybeAlign(16));
    B.CreateCall(lifted, {state, B.getInt64(0x401000)});
    B.CreateRet(B.getInt64(0));
  }

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);

  bool found_missing_handler = false;
  bool found_direct_lifted_call = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_missing_block_handler")
        found_missing_handler = true;
      if (callee->getName() == "sub_401000")
        found_direct_lifted_call = true;
    }
  }

  EXPECT_TRUE(found_missing_handler);
  EXPECT_FALSE(found_direct_lifted_call);
  EXPECT_TRUE(root_after->hasFnAttribute("omill.terminal_boundary_kind"));
  auto target_attr =
      root_after->getFnAttribute("omill.terminal_boundary_target_va");
  ASSERT_TRUE(target_attr.isValid());
  EXPECT_EQ(target_attr.getValueAsString(), "401234");
}

TEST_F(PipelineTest, LateCleanupAnnotatesTerminalBoundaryCycle) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *handler_ty = llvm::FunctionType::get(
      llvm::Type::getVoidTy(Ctx), {i64_ty}, false);
  llvm::Function::Create(handler_ty, llvm::GlobalValue::ExternalLinkage,
                         "__omill_missing_block_handler", *M);

  auto make_terminal_root = [&](llvm::StringRef name, uint64_t target_pc) {
    auto *F = llvm::Function::Create(
        llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
        llvm::GlobalValue::ExternalLinkage, name, *M);
    F->addFnAttr("omill.output_root");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
    llvm::IRBuilder<> B(entry);
    auto *callee = M->getFunction("__omill_missing_block_handler");
    auto *CI = B.CreateCall(callee, {B.getInt64(target_pc)});
    CI->setMetadata("omill.terminal_boundary",
                    llvm::MDTuple::get(Ctx, {}));
    B.CreateRet(B.getInt64(0));
    return F;
  };

  auto *a = make_terminal_root("sub_401000_native", 0x402000);
  auto *b = make_terminal_root("sub_402000_native", 0x401000);

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *a_after = M->getFunction(a->getName());
  auto *b_after = M->getFunction(b->getName());
  ASSERT_NE(a_after, nullptr);
  ASSERT_NE(b_after, nullptr);

  ASSERT_TRUE(a_after->hasFnAttribute("omill.terminal_boundary_cycle"));
  ASSERT_TRUE(b_after->hasFnAttribute("omill.terminal_boundary_cycle"));
  EXPECT_EQ(a_after->getFnAttribute("omill.terminal_boundary_cycle")
                .getValueAsString(),
            "401000,402000");
  EXPECT_EQ(b_after->getFnAttribute("omill.terminal_boundary_cycle")
                .getValueAsString(),
            "401000,402000");
  EXPECT_EQ(a_after->getFnAttribute("omill.terminal_boundary_cycle_len")
                .getValueAsString(),
            "2");
  EXPECT_EQ(b_after->getFnAttribute("omill.terminal_boundary_cycle_len")
                .getValueAsString(),
            "2");
  EXPECT_EQ(
      a_after->getFnAttribute("omill.terminal_boundary_cycle_canonical_target_va")
          .getValueAsString(),
      "401000");
  EXPECT_EQ(
      b_after->getFnAttribute("omill.terminal_boundary_cycle_canonical_target_va")
          .getValueAsString(),
      "401000");

  auto *cycles_md = M->getNamedMetadata("omill.terminal_boundary_cycles");
  ASSERT_NE(cycles_md, nullptr);
  ASSERT_EQ(cycles_md->getNumOperands(), 1u);
}

TEST_F(PipelineTest,
       LateCleanupAnnotatesTerminalBoundaryTargetForRepeatedSameTarget) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *handler_ty = llvm::FunctionType::get(
      llvm::Type::getVoidTy(Ctx), {i64_ty}, false);
  auto *handler = llvm::Function::Create(handler_ty,
                                         llvm::GlobalValue::ExternalLinkage,
                                         "__omill_missing_block_handler", *M);

  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *left = llvm::BasicBlock::Create(Ctx, "left", root);
    auto *right = llvm::BasicBlock::Create(Ctx, "right", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCondBr(B.getTrue(), left, right);

    B.SetInsertPoint(left);
    B.CreateCall(handler, {B.getInt64(0x401234ULL)});
    B.CreateRet(B.getInt64(1));

    B.SetInsertPoint(right);
    B.CreateCall(handler, {B.getInt64(0x401234ULL)});
    B.CreateRet(B.getInt64(2));
  }

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  ASSERT_TRUE(root_after->hasFnAttribute("omill.terminal_boundary_count"));
  auto target_attr =
      root_after->getFnAttribute("omill.terminal_boundary_target_va");
  ASSERT_TRUE(target_attr.isValid());
  EXPECT_EQ(target_attr.getValueAsString(), "401234");
}

TEST_F(PipelineTest,
       LateCleanupCanonicalizesTerminalBoundaryOutputRootToProbeCycleTarget) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *handler_ty = llvm::FunctionType::get(
      llvm::Type::getVoidTy(Ctx), {i64_ty}, false);
  auto *handler = llvm::Function::Create(handler_ty,
                                         llvm::GlobalValue::ExternalLinkage,
                                         "__omill_missing_block_handler", *M);

  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.terminal_boundary_probe_cycle_canonical_target_va",
                  "401100");

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(handler, {B.getInt64(0x401234ULL)});
    B.CreateRet(B.getInt64(0));
  }

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M);

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);
  ASSERT_TRUE(
      root_after->hasFnAttribute("omill.terminal_boundary_original_target_va"));
  EXPECT_EQ(root_after
                ->getFnAttribute("omill.terminal_boundary_original_target_va")
                .getValueAsString(),
            "401234");

  auto target_attr =
      root_after->getFnAttribute("omill.terminal_boundary_target_va");
  ASSERT_TRUE(target_attr.isValid());
  EXPECT_EQ(target_attr.getValueAsString(), "401100");

  bool saw_handler = false;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee || callee->getName() != "__omill_missing_block_handler")
        continue;
      auto *pc = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(0));
      ASSERT_NE(pc, nullptr);
      EXPECT_EQ(pc->getZExtValue(), 0x401100ULL);
      saw_handler = true;
    }
  }
  EXPECT_TRUE(saw_handler);
}

TEST_F(PipelineTest,
       LateCleanupPreservesExecutableInImageDeclaredLiftedHelperCall) {
  auto M = createModule();

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *callee = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_402000", *M);
  auto *root = llvm::Function::Create(
      llvm::FunctionType::get(i64_ty, {ptr_ty}, false),
      llvm::GlobalValue::ExternalLinkage, "sub_401000_native", *M);
  root->addFnAttr("omill.output_root");

  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "state_storage");
    auto *stack =
        B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), 64), nullptr,
                       "stack_storage");
    auto *state_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), state, 0);
    auto *stack_ptr = B.CreateConstGEP1_64(B.getInt8Ty(), stack, 0);
    auto *rv = B.CreateCall(callee, {state_ptr, B.getInt64(0x402000), stack_ptr});
    B.CreateRet(B.CreatePtrToInt(rv, i64_ty));
  }

  omill::BinaryMemoryMap map;
  static const uint8_t exec_bytes[16] = {0x55, 0x48, 0x89, 0xE5};
  map.setImageBase(0x400000);
  map.setImageSize(0x4000);
  map.addRegion(0x402000, exec_bytes, sizeof(exec_bytes), /*read_only=*/false,
                /*executable=*/true);

  llvm::ModulePassManager MPM;
  omill::buildLateCleanupPipeline(MPM);
  runMPM(MPM, *M, std::move(map));

  auto *root_after = M->getFunction("sub_401000_native");
  ASSERT_NE(root_after, nullptr);

  bool found_helper_call = false;
  bool found_unreachable = false;
  for (auto &BB : *root_after) {
    if (llvm::isa<llvm::UnreachableInst>(BB.getTerminator()))
      found_unreachable = true;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *called = CI->getCalledFunction();
      if (called && called->getName() == "sub_402000")
        found_helper_call = true;
    }
  }

  EXPECT_TRUE(found_helper_call);
  EXPECT_FALSE(found_unreachable);
}

TEST_F(PipelineTest, GlobalAlwaysInlineSkipSuppressesAlwaysInlinerPasses) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_401000");

  auto opts = minimalOpts();

  auto baseline_runs = collectPassRuns(*M, opts);
  bool saw_always_inliner = false;
  bool saw_module_inliner = false;
  for (const auto &run : baseline_runs) {
    if (run.first.find("AlwaysInlinerPass") != std::string::npos) {
      saw_always_inliner = true;
    }
    if (run.first.find("ModuleInlinerWrapperPass") != std::string::npos ||
        run.first.find("inline<only-mandatory>,inline") != std::string::npos) {
      saw_module_inliner = true;
    }
  }
  EXPECT_TRUE(saw_always_inliner);

  setEnv("OMILL_SKIP_ALWAYS_INLINE", "1");
  auto skipped_runs = collectPassRuns(*M, opts);
  unsetEnv("OMILL_SKIP_ALWAYS_INLINE");

  for (const auto &run : skipped_runs) {
    EXPECT_EQ(run.first.find("AlwaysInlinerPass"), std::string::npos);
    EXPECT_EQ(run.first.find("ModuleInlinerWrapperPass"), std::string::npos);
    EXPECT_EQ(run.first.find("inline<only-mandatory>,inline"),
              std::string::npos);
  }
}

TEST_F(PipelineTest,
       GenericStaticDevirtualizationCandidateDetectionIgnoresPlainLiftedRoot) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_401000");

  EXPECT_FALSE(omill::moduleHasGenericStaticDevirtualizationCandidates(*M));
  EXPECT_TRUE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/false, /*requested_root_is_export=*/false,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_TRUE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
}

TEST_F(PipelineTest,
       GenericStaticDevirtualizationCandidateDetectionKeepsExportRootWithRootLocalShape) {
  auto M = createModule();
  createDefinedFunction(*M, "sub_401000");

  EXPECT_FALSE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/true));
}

TEST_F(PipelineTest,
       GenericStaticDevirtualizationCandidateDetectionSkipsVmModuleExportWithoutRootLocalShape) {
  auto M = createModule();
  auto *root = createDefinedFunction(*M, "sub_401000");
  root->addFnAttr("omill.vm_handler");

  EXPECT_TRUE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/true, /*requested_root_is_export=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_FALSE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/true, /*requested_root_is_export=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/true));
}

TEST_F(PipelineTest, FastPlainExportRootFallbackMatchesDriverPolicy) {
  EXPECT_TRUE(omill::shouldUseFastPlainExportRootFallback(
      /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/64ull << 10,
      /*executable_section_count=*/1));
  EXPECT_FALSE(omill::shouldUseFastPlainExportRootFallback(
      /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/2ull << 20,
      /*executable_section_count=*/2));
  EXPECT_FALSE(omill::shouldUseFastPlainExportRootFallback(
      /*vm_mode=*/true, /*requested_root_is_export=*/true,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/64ull << 10,
      /*executable_section_count=*/1));
}

TEST_F(PipelineTest, StableNoGsdExportRootFallbackMatchesDriverPolicy) {
  EXPECT_TRUE(omill::shouldUseStableNoGsdExportRootFallback(
      /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/2ull << 20));
  EXPECT_FALSE(omill::shouldUseStableNoGsdExportRootFallback(
      /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/256ull << 10));
  EXPECT_FALSE(omill::shouldUseStableNoGsdExportRootFallback(
      /*vm_mode=*/false, /*requested_root_is_export=*/false,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/2ull << 20));
  EXPECT_FALSE(omill::shouldUseStableNoGsdExportRootFallback(
      /*vm_mode=*/true, /*requested_root_is_export=*/true,
      /*use_block_lifting=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*largest_executable_section_size=*/2ull << 20));
}

TEST_F(PipelineTest,
       GenericStaticDevirtualizationCandidateDetectionFindsVmHandlerAttr) {
  auto M = createModule();
  auto *root = createDefinedFunction(*M, "sub_401000");
  root->addFnAttr("omill.vm_handler");

  EXPECT_TRUE(omill::moduleHasGenericStaticDevirtualizationCandidates(*M));
  EXPECT_FALSE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/false, /*requested_root_is_export=*/false,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_TRUE(omill::shouldAutoSkipGenericStaticDevirtualizationForRoot(
      *M, /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*force_generic_static_devirtualize=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
}

TEST_F(PipelineTest, TerminalBoundaryRecoveryClassifierClosedCandidate) {
  omill::TerminalBoundaryRecoveryMetrics metrics;
  metrics.define_blk = 4;
  metrics.call_blk = 12;

  EXPECT_EQ(omill::classifyTerminalBoundaryRecoveryMetrics(metrics),
            omill::TerminalBoundaryRecoveryStatus::kClosedCandidate);
}

TEST_F(PipelineTest, TerminalBoundaryRecoveryClassifierVmLikeOpen) {
  omill::TerminalBoundaryRecoveryMetrics metrics;
  metrics.define_blk = 474;
  metrics.declare_blk = 133;
  metrics.call_blk = 702;
  metrics.dispatch_jump = 7;

  EXPECT_EQ(omill::classifyTerminalBoundaryRecoveryMetrics(metrics),
            omill::TerminalBoundaryRecoveryStatus::kVmLikeOpen);
}

TEST_F(PipelineTest, TerminalBoundaryRecoveryClassifierLargeOpen) {
  omill::TerminalBoundaryRecoveryMetrics metrics;
  metrics.define_blk = 6086;
  metrics.declare_blk = 1222;
  metrics.call_blk = 8277;
  metrics.dispatch_jump = 755;

  EXPECT_EQ(omill::classifyTerminalBoundaryRecoveryMetrics(metrics),
            omill::TerminalBoundaryRecoveryStatus::kLargeOpen);
}

TEST_F(PipelineTest, RefreshTerminalBoundaryRecoveryMetadataBuildsNamedTuple) {
  auto M = createModule();
  auto *root = createDefinedFunction(*M, "sub_401000_native");
  root->addFnAttr("omill.output_root");
  root->addFnAttr("omill.terminal_boundary_recovery_status", "vm_like_open");
  root->addFnAttr("omill.terminal_boundary_recovery_target_va", "401234");
  root->addFnAttr("omill.terminal_boundary_recovery_summary",
                  "define_blk=4,declare_blk=1");

  omill::refreshTerminalBoundaryRecoveryMetadata(*M);

  auto *recoveries = M->getNamedMetadata("omill.terminal_boundary_recoveries");
  ASSERT_NE(recoveries, nullptr);
  ASSERT_EQ(recoveries->getNumOperands(), 1u);
  auto *tuple = recoveries->getOperand(0);
  ASSERT_EQ(tuple->getNumOperands(), 4u);
  EXPECT_EQ(llvm::cast<llvm::MDString>(tuple->getOperand(0))->getString(),
            "sub_401000_native");
  EXPECT_EQ(llvm::cast<llvm::MDString>(tuple->getOperand(1))->getString(),
            "vm_like_open");
  auto *target_md =
      llvm::dyn_cast<llvm::ConstantAsMetadata>(tuple->getOperand(2));
  ASSERT_NE(target_md, nullptr);
  auto *target_ci = llvm::dyn_cast<llvm::ConstantInt>(target_md->getValue());
  ASSERT_NE(target_ci, nullptr);
  EXPECT_EQ(target_ci->getZExtValue(), 0x401234ULL);
  EXPECT_EQ(llvm::cast<llvm::MDString>(tuple->getOperand(3))->getString(),
            "define_blk=4,declare_blk=1");
}

TEST_F(PipelineTest, AutoSkipAlwaysInlineForInternalRootMatchesDriverPolicy) {
  EXPECT_TRUE(omill::shouldAutoSkipAlwaysInlineForRoot(
      /*vm_mode=*/false, /*requested_root_is_export=*/false,
      /*generic_static_devirtualize_requested=*/true,
      /*generic_static_devirtualize_enabled=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_FALSE(omill::shouldAutoSkipAlwaysInlineForRoot(
      /*vm_mode=*/true, /*requested_root_is_export=*/false,
      /*generic_static_devirtualize_requested=*/true,
      /*generic_static_devirtualize_enabled=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_FALSE(omill::shouldAutoSkipAlwaysInlineForRoot(
      /*vm_mode=*/false, /*requested_root_is_export=*/false,
      /*generic_static_devirtualize_requested=*/false,
      /*generic_static_devirtualize_enabled=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_FALSE(omill::shouldAutoSkipAlwaysInlineForRoot(
      /*vm_mode=*/false, /*requested_root_is_export=*/false,
      /*generic_static_devirtualize_requested=*/true,
      /*generic_static_devirtualize_enabled=*/true,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_FALSE(omill::shouldAutoSkipAlwaysInlineForRoot(
      /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*generic_static_devirtualize_enabled=*/false,
      /*root_local_generic_static_devirtualization_shape=*/false));
  EXPECT_FALSE(omill::shouldAutoSkipAlwaysInlineForRoot(
      /*vm_mode=*/false, /*requested_root_is_export=*/true,
      /*generic_static_devirtualize_requested=*/true,
      /*generic_static_devirtualize_enabled=*/false,
      /*root_local_generic_static_devirtualization_shape=*/true));
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
  opts.no_abi_mode = true;
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
  opts.no_abi_mode = true;
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
       ClosedSliceNoAbiCleanupCollapsesRepeatedBlkMustTailFallback) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *missing_block = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "__remill_missing_block",
      *M);

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
    auto *first =
        B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    auto *second =
        B.CreateCall(helper, {root->getArg(0), B.getInt64(0x401010ULL), first});
    B.CreateRet(second);
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
  opts.no_abi_mode = true;
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
  EXPECT_GE(calls_missing_block, 2u);
  EXPECT_EQ(M->getFunction("blk_401010"), nullptr);
}

TEST_F(PipelineTest, ClosedSliceNoAbiCleanupCollapsesInternalBlkChain) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *leaf = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_401030", *M);
  leaf->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(leaf->getArg(0));
  }

  auto *mid = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_401020", *M);
  mid->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        leaf, {mid->getArg(0), B.getInt64(0x401030ULL), mid->getArg(2)});
    B.CreateRet(call);
  }

  auto *head = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_401010", *M);
  head->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", head);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        mid, {head->getArg(0), B.getInt64(0x401020ULL), head->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->addFnAttr("omill.output_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        head, {root->getArg(0), B.getInt64(0x401010ULL), root->getArg(2)});
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
  opts.no_abi_mode = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  auto *root_after = M->getFunction("sub_401000");
  ASSERT_NE(root_after, nullptr);

  unsigned calls_blk = 0;
  for (auto &BB : *root_after) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName().starts_with("blk_"))
        ++calls_blk;
    }
  }

  EXPECT_EQ(calls_blk, 0u);
  EXPECT_EQ(M->getFunction("blk_401010"), nullptr);
  EXPECT_EQ(M->getFunction("blk_401020"), nullptr);
  EXPECT_EQ(M->getFunction("blk_401030"), nullptr);
}

TEST_F(PipelineTest, ClosedSliceNoAbiCleanupLoopifiesSelfRecursiveBlkHelper) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_401010", *M);
  helper->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    auto *recurse = llvm::BasicBlock::Create(Ctx, "recurse", helper);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper);
    auto *ret = llvm::BasicBlock::Create(Ctx, "ret", helper);

    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(i64_ty);
    B.CreateStore(B.getInt64(0x1111ULL), slot);
    auto *cond =
        B.CreateICmpEQ(helper->getArg(1), B.getInt64(0x401010ULL));
    B.CreateCondBr(cond, recurse, exit);

    B.SetInsertPoint(recurse);
    auto *call = B.CreateCall(
        helper, {helper->getArg(0), B.getInt64(0x401010ULL), helper->getArg(2)});
    auto *loaded = B.CreateLoad(i64_ty, slot);
    B.CreateStore(loaded, slot);
    auto *frozen = B.CreateFreeze(call);
    B.CreateBr(ret);

    B.SetInsertPoint(exit);
    B.CreateBr(ret);

    B.SetInsertPoint(ret);
    auto *phi = B.CreatePHI(ptr_ty, 2);
    phi->addIncoming(frozen, recurse);
    phi->addIncoming(helper->getArg(2), exit);
    B.CreateRet(phi);
  }

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->addFnAttr("omill.output_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        helper, {root->getArg(0), B.getInt64(0x401010ULL), root->getArg(2)});
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
  opts.no_abi_mode = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  unsigned self_calls = 0;
  unsigned blk_calls = 0;
  for (auto &F : *M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "blk_401010")
          ++blk_calls;
        if (callee == &F)
          ++self_calls;
      }
    }
  }

  EXPECT_EQ(self_calls, 0u);
  EXPECT_EQ(blk_calls, 0u);
}

TEST_F(PipelineTest,
       ClosedSliceNoAbiCleanupLoopifiesSelfRecursiveBlkHelperMustTailReturn) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::InternalLinkage, "blk_401110", *M);
  helper->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    auto *recurse = llvm::BasicBlock::Create(Ctx, "recurse", helper);
    auto *exit = llvm::BasicBlock::Create(Ctx, "exit", helper);

    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateAlloca(i64_ty);
    B.CreateStore(B.getInt64(0x2222ULL), slot);
    auto *cond =
        B.CreateICmpEQ(helper->getArg(1), B.getInt64(0x401110ULL));
    B.CreateCondBr(cond, recurse, exit);

    B.SetInsertPoint(recurse);
    auto *call = B.CreateCall(
        helper, {helper->getArg(0), B.getInt64(0x401110ULL), helper->getArg(2)});
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    auto *loaded = B.CreateLoad(i64_ty, slot);
    B.CreateStore(loaded, slot);
    B.CreateRet(call);

    B.SetInsertPoint(exit);
    B.CreateRet(helper->getArg(2));
  }

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401100", *M);
  root->addFnAttr("omill.closed_root_slice", "1");
  root->addFnAttr("omill.closed_root_slice_root", "1");
  root->addFnAttr("omill.output_root", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(
        helper, {root->getArg(0), B.getInt64(0x401110ULL), root->getArg(2)});
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
  opts.no_abi_mode = true;
  opts.run_cleanup_passes = false;

  runPipeline(*M, opts);

  unsigned self_calls = 0;
  unsigned blk_calls = 0;
  for (auto &F : *M) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "blk_401110")
          ++blk_calls;
        if (callee == &F)
          ++self_calls;
      }
    }
  }

  EXPECT_EQ(self_calls, 0u);
  EXPECT_EQ(blk_calls, 0u);
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

TEST_F(PipelineTest,
       NoAbiPostCleanupRebuildDropsClosedSliceTagFromSemanticHelpers) {
  auto M = createModule();
  M->addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  M->addModuleFlag(llvm::Module::Override, "omill.no_abi_mode", 1u);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *leaf = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "blk_401020", *M);
  leaf->addFnAttr("omill.closed_root_slice", "1");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", leaf);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(leaf->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "semantic_helper", *M);
  helper->addFnAttr("omill.vm_handler");
  helper->addFnAttr("omill.closed_root_slice", "1");
  helper->setMetadata("remill.function.type", llvm::MDNode::get(Ctx, {}));
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(helper->getParent()->getFunction("blk_401020"),
                              {helper->getArg(0), helper->getArg(1),
                               helper->getArg(2)});
    B.CreateRet(call);
  }

  auto *other = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_402000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", other);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(helper, {other->getArg(0), other->getArg(1), other->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(
      lifted_ty, llvm::GlobalValue::ExternalLinkage, "sub_401000", *M);
  root->addFnAttr("omill.output_root");
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
  EXPECT_TRUE(root_after->hasFnAttribute("omill.closed_root_slice"));

  unsigned closed_semantic_helpers = 0;
  for (auto &F : *M) {
    if (F.getMetadata("remill.function.type") &&
        F.hasFnAttribute("omill.closed_root_slice")) {
      ++closed_semantic_helpers;
    }
  }
  EXPECT_EQ(closed_semantic_helpers, 0u);
}

}  // namespace
