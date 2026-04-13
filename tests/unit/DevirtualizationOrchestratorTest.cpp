#include "omill/Devirtualization/Orchestrator.h"
#include "omill/BC/RemillProjectionLifter.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdlib>
#include <map>
#include <set>
#include <sstream>

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

namespace {

class DevirtualizationOrchestratorTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  static llvm::FunctionType *liftedFnTy(llvm::LLVMContext &Ctx) {
    auto *ptr_ty = llvm::PointerType::getUnqual(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    return llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  }

  static llvm::Function *addLiftedFunction(llvm::Module &M,
                                           llvm::StringRef name) {
    auto *Fn = llvm::Function::Create(liftedFnTy(M.getContext()),
                                      llvm::Function::ExternalLinkage, name, M);
    auto *Entry = llvm::BasicBlock::Create(M.getContext(), "entry", Fn);
    llvm::IRBuilder<> B(Entry);
    B.CreateRet(Fn->getArg(2));
    return Fn;
  }

  static const omill::NormalizedLiftUnitCacheEntry *findCacheEntry(
      const omill::DevirtualizationSession &session, uint64_t va) {
    for (const auto &[key, entry] : session.normalized_unit_cache) {
      if (key.va == va)
        return &entry;
    }
    return nullptr;
  }

  static llvm::Function *materializeBlockFunction(llvm::Module &M,
                                                  uint64_t pc) {
    std::stringstream ss;
    ss << "blk_" << std::hex << pc;
    const auto name = ss.str();
    if (auto *Fn = M.getFunction(name)) {
      if (Fn->isDeclaration()) {
        auto *Entry = llvm::BasicBlock::Create(M.getContext(), "entry", Fn);
        llvm::IRBuilder<> B(Entry);
        B.CreateRet(Fn->getArg(2));
      }
      return Fn;
    }
    return addLiftedFunction(M, name);
  }

  static omill::RemillProjectionLifter makeProjectionLifter(llvm::Module &M) {
    return omill::RemillProjectionLifter(
        [&](uint64_t pc,
            llvm::SmallVectorImpl<uint64_t> &discovered_targets)
            -> llvm::Function * {
          discovered_targets.clear();
          return materializeBlockFunction(M, pc);
        });
  }
};

class ScopedTestEnvVar {
 public:
  ScopedTestEnvVar(const char *name, const char *value) : name_(name) {
    if (const char *cur = std::getenv(name_)) {
      old_value_ = cur;
      had_old_value_ = true;
    }
#if defined(_WIN32)
    _putenv_s(name_, value);
#else
    setenv(name_, value, 1);
#endif
  }

  ~ScopedTestEnvVar() {
    if (had_old_value_) {
#if defined(_WIN32)
      _putenv_s(name_, old_value_.c_str());
#else
      setenv(name_, old_value_.c_str(), 1);
#endif
      return;
    }
#if defined(_WIN32)
    _putenv_s(name_, "");
#else
    unsetenv(name_);
#endif
  }

 private:
  const char *name_ = nullptr;
  bool had_old_value_ = false;
  std::string old_value_;
};

static omill::FrontierCallbacks makeFrontierCallbacks() {
  omill::FrontierCallbacks callbacks;
  callbacks.is_code_address = [](uint64_t pc) {
    return pc >= 0x401000 && pc < 0x500000;
  };
  callbacks.has_defined_target = [](uint64_t) { return false; };
  callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
  callbacks.is_executable_target = [](uint64_t) { return true; };
  callbacks.is_protected_boundary = [](uint64_t) { return false; };
  callbacks.can_decode_target = [](uint64_t) { return true; };
  callbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size == 0)
      return false;
    out[0] = 0x90;
    for (size_t i = 1; i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  return callbacks;
}

TEST_F(DevirtualizationOrchestratorTest,
       DetectsVmShapedUnresolvedDispatchAsDevirtualizationCandidate) {
  llvm::Module M("dispatch", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Helper = addLiftedFunction(M, "blk_401020_native");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__omill_dispatch_jump",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *HelperCall = B.CreateCall(
      Helper, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(HelperCall);

  auto &HelperEntry = Helper->getEntryBlock();
  HelperEntry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> HB(&HelperEntry);
  HB.CreateCall(Dispatch,
                {Helper->getArg(0), HB.getInt64(0x401020), Helper->getArg(2)});
  HB.CreateRet(Helper->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  EXPECT_FALSE(omill::moduleHasGenericStaticDevirtualizationCandidates(M));
  EXPECT_TRUE(omill::moduleHasRootLocalGenericStaticDevirtualizationShape(M));
  auto Detection = Orchestrator.detect(M, Request);
  auto Plan = Orchestrator.buildExecutionPlan(M, Request);

  EXPECT_TRUE(Detection.should_devirtualize);
  EXPECT_EQ(Detection.unresolved_dispatches, 1u);
  EXPECT_EQ(Detection.confidence, omill::DevirtualizationConfidence::kHigh);
  EXPECT_TRUE(Plan.enable_devirtualization);
  EXPECT_TRUE(Plan.use_generic_static_devirtualization);
}

TEST_F(DevirtualizationOrchestratorTest,
       DoesNotAutoDetectPlainUnresolvedDispatchWithoutVmSignals) {
  llvm::Module M("plain_dispatch", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Detection = Orchestrator.detect(M, Request);
  auto Plan = Orchestrator.buildExecutionPlan(M, Request);

  EXPECT_FALSE(Detection.should_devirtualize);
  EXPECT_EQ(Detection.unresolved_dispatches, 1u);
  EXPECT_TRUE(Detection.reasons.empty());
  EXPECT_FALSE(Plan.enable_devirtualization);
}

TEST_F(DevirtualizationOrchestratorTest,
       AutoDetectsLargeNoAbiUnresolvedDispatchFrontier) {
  llvm::Module M("compact_like_dispatch", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  for (unsigned i = 0; i < 128; ++i)
    B.CreateCall(Dispatch,
                 {Root->getArg(0), B.getInt64(0x401020 + i), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  omill::DevirtualizationCompatInputs CompatInputs;
  CompatInputs.no_abi = true;
  CompatInputs.executable_section_count = 2;
  CompatInputs.largest_executable_section_size = 300ull << 10;

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Detection = Orchestrator.detect(M, Request, CompatInputs);
  auto Plan = Orchestrator.buildExecutionPlan(M, Request, CompatInputs);

  EXPECT_TRUE(Detection.should_devirtualize);
  EXPECT_EQ(Detection.confidence, omill::DevirtualizationConfidence::kMedium);
  EXPECT_EQ(Detection.unresolved_dispatches, 128u);
  EXPECT_NE(std::find(Detection.reasons.begin(), Detection.reasons.end(),
                      "large_noabi_unresolved_dispatch_frontier"),
            Detection.reasons.end());
  EXPECT_TRUE(Plan.enable_devirtualization);
  EXPECT_TRUE(Plan.use_generic_static_devirtualization);
}


TEST_F(DevirtualizationOrchestratorTest,
       ForceModeEnablesCanonicalPipelineSettings) {
  llvm::Module M("forced", Ctx);
  addLiftedFunction(M, "sub_401000");

  omill::DevirtualizationRequest Request;
  Request.force_devirtualize = true;
  Request.verify_rewrites = true;

  omill::PipelineOptions Opts;
  omill::DevirtualizationOrchestrator Orchestrator;
  auto Plan = Orchestrator.buildExecutionPlan(M, Request);
  Orchestrator.applyExecutionPlan(Plan, Opts);

  EXPECT_TRUE(Plan.enable_devirtualization);
  EXPECT_TRUE(Opts.generic_static_devirtualize);
  EXPECT_FALSE(Opts.vm_devirtualize);
  EXPECT_TRUE(Opts.verify_generic_static_devirtualization);
  EXPECT_TRUE(Opts.require_remill_normalization);
}

TEST_F(DevirtualizationOrchestratorTest,
       DetectUsesCompatInputsAsCompatibilityRequest) {
  llvm::Module M("compat_detect", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  omill::DevirtualizationCompatInputs CompatInputs;
  CompatInputs.requested_block_lift = true;

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Detection = Orchestrator.detect(M, Request, CompatInputs);

  EXPECT_TRUE(Detection.should_devirtualize);
  EXPECT_NE(std::find(Detection.reasons.begin(), Detection.reasons.end(),
                      "compatibility_flag"),
            Detection.reasons.end());
}

TEST_F(DevirtualizationOrchestratorTest,
       DriverCompatPlanSelectsFastPlainExportRootFallback) {
  llvm::Module M("compat_fast_export", Ctx);
  addLiftedFunction(M, "sub_401000");

  omill::DevirtualizationRequest Request;
  Request.force_devirtualize = true;
  omill::DevirtualizationCompatInputs CompatInputs;
  CompatInputs.requested_root_is_export = true;
  CompatInputs.largest_executable_section_size = 64ull << 10;
  CompatInputs.executable_section_count = 1;

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Plan = Orchestrator.buildDriverCompatPlan(M, Request, CompatInputs);

  EXPECT_TRUE(Plan.execution.enable_devirtualization);
  EXPECT_EQ(Plan.export_root_fallback_mode,
            omill::DevirtualizationExportRootFallbackMode::kFastPlain);
  EXPECT_EQ(Plan.generic_static_reason,
            omill::DevirtualizationCompatReason::kFastPlainExportRootFallback);
  EXPECT_FALSE(Plan.use_generic_static);
  EXPECT_FALSE(Plan.use_pre_abi_noabi_cleanup);
}

TEST_F(DevirtualizationOrchestratorTest,
       DriverCompatPlanSelectsStableLargeExportRootFallback) {
  llvm::Module M("compat_large_export", Ctx);
  addLiftedFunction(M, "sub_401000");

  omill::DevirtualizationRequest Request;
  Request.force_devirtualize = true;
  omill::DevirtualizationCompatInputs CompatInputs;
  CompatInputs.requested_root_is_export = true;
  CompatInputs.requested_root_rva = 0x2400;
  CompatInputs.largest_executable_section_size = 2ull << 20;
  CompatInputs.executable_section_count = 2;

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Plan = Orchestrator.buildDriverCompatPlan(M, Request, CompatInputs);

  EXPECT_EQ(Plan.export_root_fallback_mode,
            omill::DevirtualizationExportRootFallbackMode::kStableLarge);
  EXPECT_EQ(Plan.generic_static_reason,
            omill::DevirtualizationCompatReason::kStableLargeExportRootFallback);
  EXPECT_TRUE(Plan.auto_skip_always_inline);
  EXPECT_EQ(Plan.always_inline_reason,
            omill::DevirtualizationCompatReason::kStableLargeExportRootFallback);
}

TEST_F(DevirtualizationOrchestratorTest,
       DriverCompatPlanKeepsPreAbiCleanupWhenVmShapeRemainsEnabled) {
  llvm::Module M("compat_pre_abi", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Helper = addLiftedFunction(M, "blk_401020_native");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__omill_dispatch_jump",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *HelperCall = B.CreateCall(
      Helper, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(HelperCall);

  auto &HelperEntry = Helper->getEntryBlock();
  HelperEntry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> HB(&HelperEntry);
  HB.CreateCall(Dispatch,
                {Helper->getArg(0), HB.getInt64(0x401020), Helper->getArg(2)});
  HB.CreateRet(Helper->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  Request.force_devirtualize = true;

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Plan = Orchestrator.buildDriverCompatPlan(M, Request, {});

  EXPECT_TRUE(Plan.root_local_generic_static_devirtualization_shape);
  EXPECT_TRUE(Plan.use_generic_static);
  EXPECT_TRUE(Plan.use_pre_abi_noabi_cleanup);
  EXPECT_TRUE(Plan.no_abi_mode);
}

TEST_F(DevirtualizationOrchestratorTest,
       DriverCompatPlanSuppressesLegacyVmModeWithoutDiscoveryLoop) {
  llvm::Module M("compat_vm_mode", Ctx);
  addLiftedFunction(M, "sub_401000");

  omill::DevirtualizationRequest ForcedRequest;
  ForcedRequest.force_devirtualize = true;
  omill::DevirtualizationCompatInputs ForcedCompatInputs;
  ForcedCompatInputs.requested_vm_entry_mode = true;

  omill::DevirtualizationOrchestrator Orchestrator;
  auto ForcedPlan =
      Orchestrator.buildDriverCompatPlan(M, ForcedRequest, ForcedCompatInputs);
  EXPECT_TRUE(ForcedPlan.suppress_legacy_vm_mode);
  EXPECT_FALSE(ForcedPlan.enable_legacy_vm_mode);
  EXPECT_EQ(ForcedPlan.legacy_vm_mode_reason,
            omill::DevirtualizationCompatReason::kLegacyVmPathSuppressed);

  omill::DevirtualizationRequest LegacyRequest;
  omill::DevirtualizationCompatInputs LegacyCompatInputs;
  LegacyCompatInputs.requested_vm_entry_mode = true;
  auto LegacyPlan =
      Orchestrator.buildDriverCompatPlan(M, LegacyRequest, LegacyCompatInputs);
  EXPECT_TRUE(LegacyPlan.suppress_legacy_vm_mode);
  EXPECT_FALSE(LegacyPlan.enable_legacy_vm_mode);
  EXPECT_EQ(LegacyPlan.legacy_vm_mode_reason,
            omill::DevirtualizationCompatReason::kLegacyVmPathSuppressed);
}

TEST_F(DevirtualizationOrchestratorTest,
       HasUnstableFrontierStateTracksPendingAndFailedGraphEdges) {
  omill::DevirtualizationOrchestrator Orchestrator;

  auto &Pending =
      Orchestrator.session().graph.edge_facts_by_identity["pending-edge"];
  Pending.identity = "pending-edge";
  Pending.status = omill::FrontierWorkStatus::kPending;
  EXPECT_TRUE(Orchestrator.hasUnstableFrontierState());

  Pending.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
  EXPECT_FALSE(Orchestrator.hasUnstableFrontierState());

  auto &Failed =
      Orchestrator.session().graph.edge_facts_by_identity["failed-edge"];
  Failed.identity = "failed-edge";
  Failed.status = omill::FrontierWorkStatus::kFailedLift;
  EXPECT_TRUE(Orchestrator.hasUnstableFrontierState());
}

TEST_F(DevirtualizationOrchestratorTest,
       HasBlockingUnstableFrontierStateIgnoresMaterializedStructuralTargets) {
  llvm::Module M("blocking_frontier_state", Ctx);
  auto *Decl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401020", M);
  Decl->addFnAttr("omill.executable_target_pc", "401020");

  omill::DevirtualizationOrchestrator Orchestrator;
  auto &StablePending =
      Orchestrator.session().graph.edge_facts_by_identity["stable-pending"];
  StablePending.identity = "stable-pending";
  StablePending.target_pc = 0x401020u;
  StablePending.kind = omill::FrontierWorkKind::kUnknownExecutableTarget;
  StablePending.status = omill::FrontierWorkStatus::kPending;

  EXPECT_TRUE(Orchestrator.hasUnstableFrontierState());
  EXPECT_FALSE(Orchestrator.hasBlockingUnstableFrontierState(M));

  auto &Blocking =
      Orchestrator.session().graph.edge_facts_by_identity["blocking-pending"];
  Blocking.identity = "blocking-pending";
  Blocking.target_pc = 0x401030u;
  Blocking.kind = omill::FrontierWorkKind::kLiftableBlock;
  Blocking.status = omill::FrontierWorkStatus::kPending;

  EXPECT_TRUE(Orchestrator.hasBlockingUnstableFrontierState(M));
}

TEST_F(DevirtualizationOrchestratorTest,
       RefreshSessionStateRebuildsGraphAfterModuleMutation) {
  llvm::Module M("refresh_graph", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void)Orchestrator.buildExecutionPlan(M, Request);
  EXPECT_FALSE(Orchestrator.hasUnstableFrontierState());

  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);
  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  Orchestrator.refreshSessionState(M);
  EXPECT_TRUE(Orchestrator.hasUnstableFrontierState());
  const auto FrontierIdentities =
      omill::collectSessionFrontierIdentities(Orchestrator.session());
  EXPECT_TRUE(std::any_of(
      FrontierIdentities.begin(), FrontierIdentities.end(),
      [](const std::string &identity) {
        return identity.find("sub_401000:0:") != std::string::npos;
      }));
}

TEST_F(DevirtualizationOrchestratorTest,
       BuildExecutionPlanPopulatesSessionAndFreshNormalizedCache) {
  llvm::Module M("session_state", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Helper = addLiftedFunction(M, "block_401020");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *HelperCall = B.CreateCall(
      Helper, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(HelperCall);

  auto &HelperEntry = Helper->getEntryBlock();
  HelperEntry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> HB(&HelperEntry);
  HB.CreateCall(Dispatch,
                {Helper->getArg(0), HB.getInt64(0x401020), Helper->getArg(2)});
  HB.CreateRet(Helper->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Plan = Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  ASSERT_TRUE(Plan.enable_devirtualization);
  ASSERT_EQ(Session.root_slice.size(), 1u);
  EXPECT_EQ(Session.root_slice.front(), 0x401000u);
  const auto FrontierTargets = omill::collectSessionFrontierTargets(Session);
  EXPECT_TRUE(std::find(FrontierTargets.begin(), FrontierTargets.end(),
                        0x401020u) != FrontierTargets.end());
  EXPECT_FALSE(Session.unresolved_exits.empty());
  EXPECT_EQ(Session.latest_round.units_lifted, 2u);
  EXPECT_EQ(Session.latest_round.units_reused, 0u);
  EXPECT_EQ(Session.latest_round.unresolved_exits_complete, 1u);

  auto *RootCache = findCacheEntry(Session, 0x401000);
  ASSERT_NE(RootCache, nullptr);
  EXPECT_EQ(RootCache->status, omill::LiftUnitCacheStatus::kFresh);
  EXPECT_TRUE(RootCache->normalization_gate_passed);

  auto *HelperCache = findCacheEntry(Session, 0x401020);
  ASSERT_NE(HelperCache, nullptr);
  EXPECT_EQ(HelperCache->status, omill::LiftUnitCacheStatus::kFresh);
}

TEST_F(DevirtualizationOrchestratorTest,
       BuildExecutionPlanReusesNormalizedCacheWhenModuleShapeIsStable) {
  llvm::Module M("cache_reuse", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Helper = addLiftedFunction(M, "block_401020");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *HelperCall = B.CreateCall(
      Helper, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(HelperCall);

  auto &HelperEntry = Helper->getEntryBlock();
  HelperEntry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> HB(&HelperEntry);
  HB.CreateCall(Dispatch,
                {Helper->getArg(0), HB.getInt64(0x401020), Helper->getArg(2)});
  HB.CreateRet(Helper->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);
  auto Plan = Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  ASSERT_TRUE(Plan.enable_devirtualization);
  EXPECT_EQ(Session.latest_round.units_lifted, 0u);
  EXPECT_EQ(Session.latest_round.units_reused, 2u);
  EXPECT_TRUE(Session.newly_lifted_functions.empty());

  auto *RootCache = findCacheEntry(Session, 0x401000);
  ASSERT_NE(RootCache, nullptr);
  EXPECT_EQ(RootCache->status, omill::LiftUnitCacheStatus::kReused);
}

TEST_F(DevirtualizationOrchestratorTest,
       UnresolvedExitInvalidatesWhenPredecessorCountChanges) {
  llvm::Module M("exit_invalidated", Ctx);
  auto *Root = llvm::Function::Create(liftedFnTy(Ctx),
                                      llvm::Function::ExternalLinkage,
                                      "sub_401000", M);
  addLiftedFunction(M, "blk_401020");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto *Entry = llvm::BasicBlock::Create(Ctx, "entry", Root);
  auto *DispatchBB = llvm::BasicBlock::Create(Ctx, "dispatch", Root);
  {
    llvm::IRBuilder<> B(Entry);
    B.CreateBr(DispatchBB);
  }
  {
    llvm::IRBuilder<> B(DispatchBB);
    B.CreateCall(Dispatch,
                 {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
    B.CreateRet(Root->getArg(2));
  }

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);

  auto *Alt = llvm::BasicBlock::Create(Ctx, "alt", Root);
  Entry->getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(Entry);
    B.CreateCondBr(llvm::ConstantInt::getTrue(Ctx), DispatchBB, Alt);
  }
  {
    llvm::IRBuilder<> B(Alt);
    B.CreateBr(DispatchBB);
  }

  (void) Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();
  auto It = std::find_if(Session.unresolved_exits.begin(),
                         Session.unresolved_exits.end(),
                         [](const omill::UnresolvedExitSite &site) {
                           return site.kind ==
                                      omill::UnresolvedExitKind::kDispatchJump &&
                                  site.target_pc.has_value() &&
                                  *site.target_pc == 0x401020u;
                         });
  ASSERT_NE(It, Session.unresolved_exits.end());
  EXPECT_EQ(It->completeness, omill::ExitCompleteness::kInvalidated);
  EXPECT_EQ(It->evidence.invalidation_reason, "predecessor_count_changed");
}

TEST_F(DevirtualizationOrchestratorTest,
       NormalizationGateMarksCacheEntryDirtyWhenLegacyDispatchAndRuntimeRemain) {
  llvm::Module M("normalization_gate", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__omill_dispatch_call",
      M);
  auto *ReadTy = llvm::FunctionType::get(
      llvm::Type::getInt8Ty(Ctx),
      {llvm::PointerType::getUnqual(Ctx), llvm::Type::getInt64Ty(Ctx)},
      false);
  auto *Read = llvm::Function::Create(ReadTy, llvm::Function::ExternalLinkage,
                                      "__remill_read_memory_8", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Read, {Root->getArg(0), B.getInt64(0x10)});
  B.CreateCall(Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  auto *RootCache = findCacheEntry(Session, 0x401000);
  ASSERT_NE(RootCache, nullptr);
  EXPECT_FALSE(RootCache->normalization_gate_passed);
  EXPECT_EQ(Session.latest_round.normalization_failures, 1u);
  EXPECT_NE(std::find(Session.dirty_functions.begin(), Session.dirty_functions.end(),
                      "sub_401000"),
            Session.dirty_functions.end());
}

TEST_F(DevirtualizationOrchestratorTest,
       EpochSummaryCarriesRoundTelemetryAndNormalizationDiagnostics) {
  llvm::Module M("epoch_summary", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__omill_dispatch_jump",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);
  auto Summary = Orchestrator.summarizeEpoch(
      omill::DevirtualizationEpoch::kNormalizationCacheAdmission, M,
      omill::DevirtualizationOutputMode::kNoABI, /*changed=*/true,
      "normalized cache refreshed");

  EXPECT_EQ(Summary.units_lifted, 1u);
  EXPECT_EQ(Summary.normalization_failures, 1u);
  EXPECT_FALSE(Summary.normalization_diagnostics.empty());
  EXPECT_NE(std::find(Summary.normalization_diagnostics.begin(),
                      Summary.normalization_diagnostics.end(),
                      "legacy_omill_dispatch_present"),
            Summary.normalization_diagnostics.end());
}

TEST_F(DevirtualizationOrchestratorTest,
       TracksVipStatusInUnresolvedExitsAndNormalizedCache) {
  llvm::Module M("vip_tracking", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch, {Root->getArg(0), Root->getArg(1), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  ASSERT_EQ(Session.unresolved_exits.size(), 1u);
  EXPECT_TRUE(Session.unresolved_exits.front().vip_symbolic);
  EXPECT_EQ(Session.unresolved_exits.front().exit_disposition,
            omill::VirtualExitDisposition::kStayInVm);

  auto *RootCache = findCacheEntry(Session, 0x401000);
  ASSERT_NE(RootCache, nullptr);
  EXPECT_EQ(RootCache->vip_status, omill::VipTrackingStatus::kSymbolic);
  EXPECT_FALSE(RootCache->vip_pc.has_value());
}

TEST_F(DevirtualizationOrchestratorTest,
       InvalidatesCacheWhenSecondExitSiteVipContextChanges) {
  llvm::Module M("vip_context_invalidation", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch,
               {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  auto *SecondDispatch = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401040), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);
  auto *FirstRootCache = findCacheEntry(Orchestrator.session(), 0x401000);
  ASSERT_NE(FirstRootCache, nullptr);
  const auto FirstFingerprint = FirstRootCache->vip_context_fingerprint;
  EXPECT_FALSE(FirstFingerprint.empty());

  SecondDispatch->setArgOperand(
      1, llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), 0x401060));

  (void) Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  auto *RootCache = findCacheEntry(Session, 0x401000);
  ASSERT_NE(RootCache, nullptr);
  EXPECT_EQ(RootCache->status, omill::LiftUnitCacheStatus::kInvalidated);
  EXPECT_NE(RootCache->vip_context_fingerprint, FirstFingerprint);
  EXPECT_NE(std::find(Session.dirty_functions.begin(), Session.dirty_functions.end(),
                      "sub_401000"),
            Session.dirty_functions.end());

  auto It = std::find_if(
      Session.unresolved_exits.begin(), Session.unresolved_exits.end(),
      [](const omill::UnresolvedExitSite &site) {
        return site.owner_function == "sub_401000" && site.site_index == 1 &&
               site.target_pc.has_value() && *site.target_pc == 0x401060u;
      });
  ASSERT_NE(It, Session.unresolved_exits.end());
  const auto FrontierIdentities = omill::collectSessionFrontierIdentities(Session);
  EXPECT_TRUE(std::any_of(
      FrontierIdentities.begin(), FrontierIdentities.end(),
      [](const std::string &identity) {
        return identity.find("sub_401000:1:") != std::string::npos &&
               identity.find(":401060:401060:") != std::string::npos;
      }));
}

TEST_F(DevirtualizationOrchestratorTest,
       InvalidatesExitWhenContinuationVipChanges) {
  llvm::Module M("continuation_vip_invalidation", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  addLiftedFunction(M, "blk_401020");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_function_call",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *Call = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "401080"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void)Orchestrator.buildExecutionPlan(M, Request);

  Call->removeFnAttr("omill.virtual_exit_continuation_vip");
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "4010A0"));

  (void)Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();
  auto It = std::find_if(
      Session.unresolved_exits.begin(), Session.unresolved_exits.end(),
      [](const omill::UnresolvedExitSite &site) {
        return site.owner_function == "sub_401000" &&
               site.kind == omill::UnresolvedExitKind::kDispatchCall &&
               site.target_pc && *site.target_pc == 0x401020u;
      });
  ASSERT_NE(It, Session.unresolved_exits.end());
  EXPECT_EQ(It->completeness, omill::ExitCompleteness::kInvalidated);
  EXPECT_EQ(It->evidence.invalidation_reason, "continuation_vip_changed");
  ASSERT_TRUE(It->continuation_vip_pc.has_value());
  EXPECT_EQ(*It->continuation_vip_pc, 0x4010A0u);
}

TEST_F(DevirtualizationOrchestratorTest,
       KeepsDistinctContinuationIdentitiesForRepeatedTargetWithDifferentVipState) {
  llvm::Module M("continuation_identities", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  addLiftedFunction(M, "blk_401020");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_function_call",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *First = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "401080"));

  auto *Second = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "4010A0"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void)Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  EXPECT_EQ(Session.discovered_continuations.size(), 1u);
  ASSERT_EQ(Session.discovered_continuation_identities.size(), 2u);
  EXPECT_NE(Session.discovered_continuation_identities[0],
            Session.discovered_continuation_identities[1]);
  EXPECT_TRUE(std::any_of(
      Session.discovered_continuation_identities.begin(),
      Session.discovered_continuation_identities.end(),
      [](const std::string &identity) {
        return identity.find(":401020:401020:401080:") != std::string::npos;
      }));
  EXPECT_TRUE(std::any_of(
      Session.discovered_continuation_identities.begin(),
      Session.discovered_continuation_identities.end(),
      [](const std::string &identity) {
        return identity.find(":401020:401020:4010A0:") != std::string::npos;
      }));
}

TEST_F(DevirtualizationOrchestratorTest,
       ReusesContinuationIdentityWhenVipStateIsStableAcrossRounds) {
  llvm::Module M("continuation_convergence", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  addLiftedFunction(M, "blk_401020");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_function_call",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *Call = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "401080"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void)Orchestrator.buildExecutionPlan(M, Request);
  const auto FirstIdentities =
      Orchestrator.session().discovered_continuation_identities;

  (void)Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  EXPECT_EQ(Session.latest_round.units_reused, 2u);
  EXPECT_TRUE(Session.dirty_functions.empty());
  EXPECT_EQ(Session.discovered_continuation_identities, FirstIdentities);
  ASSERT_EQ(Session.discovered_continuation_identities.size(), 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       TracksDistinctFrontierIdentitiesForRepeatedTargetPcSites) {
  llvm::Module M("vip_frontier_identities", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Dispatch,
               {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateCall(Dispatch,
               {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void) Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  const auto FrontierItems = omill::collectSessionFrontierWorkItems(Session);
  const auto FrontierIdentities = omill::collectSessionFrontierIdentities(Session);
  const auto PendingItems = omill::collectPendingSessionFrontierWorkItems(Session);
  ASSERT_EQ(FrontierIdentities.size(), 2u);
  EXPECT_EQ(PendingItems.size(), 2u);

  std::set<std::string> DistinctIdentities(FrontierIdentities.begin(),
                                           FrontierIdentities.end());
  EXPECT_EQ(DistinctIdentities.size(), 2u);
  std::set<std::string> DistinctWorkItemIdentities;
  for (const auto &item : FrontierItems)
    DistinctWorkItemIdentities.insert(item.identity);
  EXPECT_EQ(DistinctWorkItemIdentities.size(), 2u);

  std::vector<unsigned> SiteIndices;
  for (const auto &site : Session.unresolved_exits) {
    if (site.owner_function == "sub_401000" && site.target_pc &&
        *site.target_pc == 0x401020u) {
      SiteIndices.push_back(site.site_index);
    }
  }
  std::sort(SiteIndices.begin(), SiteIndices.end());
  ASSERT_EQ(SiteIndices.size(), 2u);
  EXPECT_EQ(SiteIndices[0], 0u);
  EXPECT_EQ(SiteIndices[1], 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       TracksDistinctFrontierWorkItemsForSameTargetPcWithDifferentContinuationVip) {
  llvm::Module M("vip_frontier_work_items", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_function_call",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *First = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "401080"));

  auto *Second = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "4010A0"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void)Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  const auto FrontierItems = omill::collectSessionFrontierWorkItems(Session);
  ASSERT_EQ(FrontierItems.size(), 2u);
  EXPECT_TRUE(std::all_of(
      FrontierItems.begin(), FrontierItems.end(),
      [](const omill::FrontierWorkItem &item) {
        return item.target_pc && *item.target_pc == 0x401020u &&
               item.boundary.has_value() &&
               omill::virtualExitDispositionFromBoundaryDisposition(
                   item.boundary->exit_disposition) ==
                   omill::VirtualExitDisposition::kVmExitNativeCallReenter;
      }));

  std::set<std::optional<uint64_t>> ContinuationVips;
  std::set<std::string> Identities;
  for (const auto &item : FrontierItems) {
    ContinuationVips.insert(item.boundary ? item.boundary->continuation_vip_pc
                                          : std::nullopt);
    Identities.insert(item.identity);
  }
  EXPECT_EQ(ContinuationVips.size(), 2u);
  EXPECT_TRUE(ContinuationVips.count(0x401080u) == 1u);
  EXPECT_TRUE(ContinuationVips.count(0x4010A0u) == 1u);
  EXPECT_EQ(Identities.size(), 2u);
  EXPECT_EQ(ContinuationVips.size(), 2u);
  EXPECT_TRUE(ContinuationVips.count(0x401080u) == 1u);
  EXPECT_TRUE(ContinuationVips.count(0x4010A0u) == 1u);
  EXPECT_EQ(Identities.size(), 2u);
}

TEST_F(DevirtualizationOrchestratorTest,
       KeepsLoopLikeFrontierRoundsDistinctWhenSameTargetPcHasDifferentVipState) {
  llvm::Module M("vip_loop_frontier_rounds", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_function_call",
      M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *First = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401000), Root->getArg(2)});
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "401080"));

  auto *Second = B.CreateCall(
      Dispatch, {Root->getArg(0), B.getInt64(0x401000), Root->getArg(2)});
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition",
                           "vm_exit_native_call_reenter"));
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "4010A0"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);

  omill::DevirtualizationOrchestrator Orchestrator;
  (void)Orchestrator.buildExecutionPlan(M, Request);
  const auto &Session = Orchestrator.session();

  const auto PendingItems = omill::collectPendingSessionFrontierWorkItems(Session);
  std::vector<uint64_t> PendingTargets;
  PendingTargets.reserve(PendingItems.size());
  for (const auto &item : PendingItems) {
    if (item.target_pc)
      PendingTargets.push_back(*item.target_pc);
  }
  ASSERT_EQ(PendingTargets.size(), 2u);
  EXPECT_EQ(PendingTargets[0], 0x401000u);
  EXPECT_EQ(PendingTargets[1], 0x401000u);
  ASSERT_EQ(PendingItems.size(), 2u);

  std::set<std::optional<uint64_t>> ContinuationVips;
  for (const auto &item : PendingItems)
    ContinuationVips.insert(item.boundary ? item.boundary->continuation_vip_pc
                                          : std::nullopt);
  EXPECT_EQ(ContinuationVips.size(), 2u);
  EXPECT_TRUE(ContinuationVips.count(0x401080u) == 1u);
  EXPECT_TRUE(ContinuationVips.count(0x4010A0u) == 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       DiscoverFrontierWorkPromotesOutputRootJumpToSessionState) {
  llvm::Module M("closure_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x401120), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto Summary = Orchestrator.discoverFrontierWork(
      M, makeFrontierCallbacks(), omill::FrontierDiscoveryPhase::kOutputRootClosure);

  EXPECT_GE(Summary.discovered, 1u);
  const auto &Session = Orchestrator.session();
  const auto FrontierItems = omill::collectSessionFrontierWorkItems(Session);
  auto It = std::find_if(FrontierItems.begin(), FrontierItems.end(),
                         [](const omill::FrontierWorkItem &item) {
                           return item.target_pc.has_value() &&
                                  *item.target_pc == 0x401120u &&
                                  item.identity.find("closure:") == 0;
                         });
  ASSERT_NE(It, FrontierItems.end());
  EXPECT_EQ(It->status, omill::FrontierWorkStatus::kPending);
  EXPECT_FALSE(It->identity.empty());
}

TEST_F(DevirtualizationOrchestratorTest,
       DiscoverFrontierWorkKeepsDistinctVipContextsForSameTarget) {
  llvm::Module M("vip_distinct_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *First = B.CreateCall(
      Jump, {Root->getArg(0), B.getInt64(0x401120), Root->getArg(2)});
  First->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "0x5000"));
  auto *Second = B.CreateCall(
      Jump, {Root->getArg(0), B.getInt64(0x401120), Root->getArg(2)});
  Second->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "0x6000"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);
  (void)Orchestrator.discoverFrontierWork(
      M, makeFrontierCallbacks(), omill::FrontierDiscoveryPhase::kOutputRootClosure);

  unsigned matching = 0;
  std::set<std::optional<uint64_t>> continuation_vips;
  for (const auto &item :
       omill::collectSessionFrontierWorkItems(Orchestrator.session())) {
    if (item.target_pc && *item.target_pc == 0x401120u &&
        item.identity.find("closure:") == 0) {
      ++matching;
      continuation_vips.insert(item.boundary ? item.boundary->continuation_vip_pc
                                             : std::nullopt);
    }
  }
  EXPECT_GE(matching, 2u);
  EXPECT_EQ(continuation_vips.size(), 2u);
  EXPECT_TRUE(continuation_vips.count(0x5000u) == 1u);
  EXPECT_TRUE(continuation_vips.count(0x6000u) == 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       DiscoverFrontierWorkPreservesCalleeBoundaryContinuationMetadataForClosureItems) {
  llvm::Module M("closure_boundary_metadata", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *VmEnterDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_4011C0", M);

  omill::BoundaryFact callee_boundary;
  callee_boundary.boundary_pc = 0x4011c0u;
  callee_boundary.continuation_pc = 0x4011d3u;
  callee_boundary.continuation_owner_id = 9u;
  callee_boundary.continuation_owner_kind =
      omill::VirtualStackOwnerKind::kFramePointerLike;
  callee_boundary.controlled_return_pc = 0x401280u;
  callee_boundary.return_address_control_kind =
      omill::VirtualReturnAddressControlKind::kRedirectedConstant;
  callee_boundary.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  callee_boundary.kind = omill::BoundaryKind::kVmEnterBoundary;
  callee_boundary.is_vm_enter = true;
  callee_boundary.reenters_vm = true;
  callee_boundary.suppresses_normal_fallthrough = true;
  callee_boundary.continuation_entry_transform =
      omill::ContinuationEntryTransform{
          omill::ContinuationEntryTransformKind::kPushImmediateJump, 0x4011c0u,
          0x401340u, 0x1234u, true};
  omill::writeBoundaryFact(*VmEnterDecl, callee_boundary);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *Call =
      B.CreateCall(VmEnterDecl, {Root->getArg(0), B.getInt64(0x4011c0),
                                 Root->getArg(2)});
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_disposition", "unknown"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto Summary = Orchestrator.discoverFrontierWork(
      M, makeFrontierCallbacks(), omill::FrontierDiscoveryPhase::kOutputRootClosure);

  EXPECT_GE(Summary.discovered, 1u);
  const auto FrontierItems =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto It = std::find_if(
      FrontierItems.begin(), FrontierItems.end(),
      [](const omill::FrontierWorkItem &item) {
        return item.identity.find("closure:") == 0 && item.target_pc &&
               *item.target_pc == 0x4011c0u;
      });
  ASSERT_NE(It, FrontierItems.end());
  ASSERT_TRUE(It->boundary.has_value());
  EXPECT_EQ(It->boundary->exit_disposition, omill::BoundaryDisposition::kVmEnter);
  EXPECT_EQ(It->boundary->continuation_owner_id, 9u);
  EXPECT_EQ(It->boundary->continuation_owner_kind,
            omill::VirtualStackOwnerKind::kFramePointerLike);
  EXPECT_EQ(It->boundary->controlled_return_pc, 0x401280u);
  EXPECT_TRUE(It->boundary->continuation_entry_transform.has_value());
  EXPECT_EQ(It->continuation_rationale, "return_address_controlled");
  EXPECT_EQ(It->scheduling_class, omill::FrontierSchedulingClass::kTrustedLive);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesNativeCallBoundaryWithoutDroppingIt) {
  llvm::Module M("native_boundary_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *Call = B.CreateCall(
      Jump, {Root->getArg(0), B.getInt64(0x401140), Root->getArg(2)});
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "0x401180"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size == 0)
      return false;
    out[0] = 0xE8;
    for (size_t i = 1; i < size; ++i)
      out[i] = 0;
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return false; };

  (void)Orchestrator.discoverFrontierWork(
      M, CallBoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_native_exit, 1u);
  auto *BoundaryDecl = M.getFunction("sub_401140");
  ASSERT_NE(BoundaryDecl, nullptr);
  EXPECT_TRUE(BoundaryDecl->isDeclaration());
  auto BoundaryFact = omill::readBoundaryFact(*BoundaryDecl);
  ASSERT_TRUE(BoundaryFact.has_value());
  EXPECT_EQ(omill::virtualExitDispositionFromBoundaryDisposition(
                BoundaryFact->exit_disposition),
            omill::VirtualExitDisposition::kVmExitNativeCallReenter);
  EXPECT_TRUE(BoundaryDecl->hasFnAttribute("omill.virtual_exit_native_target_pc"));
  EXPECT_EQ(BoundaryDecl->getFnAttribute("omill.virtual_exit_native_target_pc")
                .getValueAsString(),
            "401145");
  EXPECT_TRUE(BoundaryDecl->hasFnAttribute("omill.virtual_exit_partial"));
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkMaterializesNativeCallReenterStubWhenContinuationExists) {
  llvm::Module M("native_boundary_reenter_stub", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Continuation = addLiftedFunction(M, "blk_401145");
  Continuation->addFnAttr("omill.closed_root_slice", "1");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *Call = B.CreateCall(
      Jump, {Root->getArg(0), B.getInt64(0x401140), Root->getArg(2)});
  Call->addAttributeAtIndex(
      llvm::AttributeList::FunctionIndex,
      llvm::Attribute::get(Ctx, "omill.virtual_exit_continuation_vip",
                           "0x401145"));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 8)
      return false;
    const uint8_t bytes[8] = {0xE8, 0x3B, 0x00, 0x00,
                              0x00, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, CallBoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_native_exit, 1u);
  auto *Boundary = M.getFunction("sub_401140");
  ASSERT_NE(Boundary, nullptr);
  EXPECT_FALSE(Boundary->isDeclaration());
  EXPECT_TRUE(Boundary->hasFnAttribute("omill.virtual_exit_continuation_pc"));
  EXPECT_EQ(Boundary->getFnAttribute("omill.virtual_exit_continuation_pc")
                .getValueAsString(),
            "401145");

  bool saw_native = false;
  bool saw_continuation = false;
  for (auto &BB : *Boundary) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      if (CB->getCalledFunction()->getName() == "omill_native_target_401180")
        saw_native = true;
      if (CB->getCalledFunction()->getName() == "blk_401145")
        saw_continuation = true;
    }
  }
  EXPECT_TRUE(saw_native);
  EXPECT_TRUE(saw_continuation);
}

TEST_F(DevirtualizationOrchestratorTest,
       BoundaryContinuationWorkMaterializesNativeReenterBridgeWhenContinuationExists) {
  llvm::Module M("boundary_continuation_reenter_bridge", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Continuation = addLiftedFunction(M, "blk_401145");
  auto *BoundaryDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "sub_401140", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(BoundaryDecl, {Root->getArg(0), B.getInt64(0x401140),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401140u;
  boundary_fact.native_target_pc = 0x401140u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 8)
      return false;
    const uint8_t bytes[8] = {0xE8, 0x3B, 0x00, 0x00,
                              0x00, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x401145u;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_TRUE(Summary.changed);
  auto *Boundary = M.getFunction("sub_401140");
  ASSERT_NE(Boundary, nullptr);
  EXPECT_FALSE(Boundary->isDeclaration());

  bool saw_native = false;
  bool saw_continuation = false;
  for (auto &BB : *Boundary) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      saw_native |= CB->getCalledFunction()->getName() ==
                    "omill_native_target_401180";
      saw_continuation |=
          CB->getCalledFunction()->getName() == "blk_401145";
    }
  }
  EXPECT_TRUE(saw_native);
  EXPECT_TRUE(saw_continuation);
}

TEST_F(DevirtualizationOrchestratorTest,
       BoundaryContinuationWorkRecoversNearbyCoveredContinuationSeed) {
  llvm::Module M("boundary_continuation_recovered_seed", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *ContinuationSeed = addLiftedFunction(M, "blk_401140");
  auto *BoundaryDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "sub_401120", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(BoundaryDecl, {Root->getArg(0), B.getInt64(0x401120),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401120u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 8)
      return false;
    const uint8_t bytes[8] = {0xE8, 0x5B, 0x00, 0x00,
                              0x00, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x401140u;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t pc) {
    return pc == 0x401140u;
  };
  CallBoundaryCallbacks.decode_target_summary =
      [](uint64_t pc)
          -> std::optional<omill::FrontierCallbacks::DecodedTargetSummary> {
    if (pc != 0x401140u)
      return std::nullopt;
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = 0x401140u;
    summary.next_pc = 0x401145u;
    summary.is_control_flow = false;
    return summary;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_TRUE(Summary.changed);
  auto *Boundary = M.getFunction("sub_401120");
  ASSERT_NE(Boundary, nullptr);
  EXPECT_FALSE(Boundary->isDeclaration());

  bool saw_native = false;
  bool saw_continuation = false;
  for (auto &BB : *Boundary) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      saw_native |= CB->getCalledFunction()->getName() ==
                    "omill_native_target_401180";
      saw_continuation |=
          CB->getCalledFunction()->getName() == ContinuationSeed->getName();
    }
  }
  EXPECT_TRUE(saw_native);
  EXPECT_TRUE(saw_continuation);
}

TEST_F(DevirtualizationOrchestratorTest,
       BoundaryContinuationWorkMaterializesBridgeUsingNearbyStructuralVmEnterPlaceholder) {
  llvm::Module M("boundary_continuation_nearby_structural_vmenter", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *BoundaryDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "sub_401120", M);
  auto *VmEnterPlaceholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_401140", M);
  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x401140u;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterPlaceholder, vm_enter_fact);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(BoundaryDecl, {Root->getArg(0), B.getInt64(0x401120),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401120u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 8)
      return false;
    const uint8_t bytes[8] = {0xE8, 0x5B, 0x00, 0x00,
                              0x00, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x401145u;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_TRUE(Summary.changed);
  auto *Boundary = M.getFunction("sub_401120");
  ASSERT_NE(Boundary, nullptr);
  EXPECT_FALSE(Boundary->isDeclaration());

  bool saw_native = false;
  for (auto &BB : *Boundary) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      saw_native |= CB->getCalledFunction()->getName() ==
                    "omill_native_target_401180";
    }
  }
  EXPECT_TRUE(saw_native);
}

TEST_F(DevirtualizationOrchestratorTest,
       BoundaryContinuationWorkPreservesExistingNativeTargetBoundaryIdentity) {
  llvm::Module M("boundary_continuation_preserve_native_target_identity", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *BoundaryDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "sub_401120", M);
  auto *VmEnterPlaceholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_401140", M);
  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x401140u;
  vm_enter_fact.native_target_pc = 0x401180u;
  vm_enter_fact.continuation_pc = 0x401145u;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterPlaceholder, vm_enter_fact);

  auto *ExistingNativeTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401180", M);
  omill::BoundaryFact existing_native_fact;
  existing_native_fact.boundary_pc = 0x401120u;
  existing_native_fact.native_target_pc = 0x401180u;
  existing_native_fact.continuation_pc = 0x401145u;
  existing_native_fact.reenters_vm = true;
  existing_native_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  existing_native_fact.kind = omill::BoundaryKind::kNativeBoundary;
  omill::writeBoundaryFact(*ExistingNativeTarget, existing_native_fact);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(BoundaryDecl, {Root->getArg(0), B.getInt64(0x401120),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401120u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 8)
      return false;
    const uint8_t bytes[8] = {0xE8, 0x5B, 0x00, 0x00,
                              0x00, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x401145u;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_TRUE(Summary.changed);
  auto fact = omill::readBoundaryFact(*ExistingNativeTarget);
  ASSERT_TRUE(fact.has_value());
  EXPECT_EQ(fact->boundary_pc, std::optional<uint64_t>(0x401120u));
  EXPECT_EQ(fact->native_target_pc, std::optional<uint64_t>(0x401180u));
  EXPECT_EQ(fact->kind, omill::BoundaryKind::kNativeBoundary);
}

TEST_F(DevirtualizationOrchestratorTest,
       BoundaryContinuationWorkPrefersImportedVmEnterRootOverPlaceholder) {
  llvm::Module M("boundary_continuation_prefers_imported_vm_enter_root", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *BoundaryDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "sub_401120", M);
  auto *VmEnterPlaceholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_401140", M);
  auto *ImportedVmEnterRoot = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::InternalLinkage,
      "tbrec_sub_401140", M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", ImportedVmEnterRoot);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(ImportedVmEnterRoot->getArg(2));
  }
  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x401140u;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterPlaceholder, vm_enter_fact);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(BoundaryDecl, {Root->getArg(0), B.getInt64(0x401120),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401120u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  Orchestrator.session().imported_vm_enter_child_roots[0x401140u] =
      ImportedVmEnterRoot->getName().str();
  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 8)
      return false;
    const uint8_t bytes[8] = {0xE8, 0x5B, 0x00, 0x00,
                              0x00, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x401145u;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_TRUE(Summary.changed);
  auto *Boundary = M.getFunction("sub_401120");
  ASSERT_NE(Boundary, nullptr);
  ASSERT_FALSE(Boundary->isDeclaration());

  bool saw_placeholder = false;
  for (auto &BB : *Boundary) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      saw_placeholder |=
          CB->getCalledFunction()->getName() == VmEnterPlaceholder->getName();
    }
  }
  EXPECT_FALSE(saw_placeholder);
}

TEST_F(DevirtualizationOrchestratorTest,
       EnqueueBoundaryContinuationWorkPromotesNearbyTrackedSeed) {
  llvm::Module M("boundary_continuation_promotes_nearby_seed", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  omill::FrontierWorkItem Nearby;
  Nearby.owner_function = "sub_401000";
  Nearby.site_index = 0;
  Nearby.site_pc = 0x401000u;
  Nearby.target_pc = 0x401140u;
  Nearby.identity = "closure:nearby";
  Nearby.executable_target = omill::ExecutableTargetFact{};
  Nearby.executable_target->raw_target_pc = 0x401140u;
  Nearby.executable_target->effective_target_pc = 0x401140u;
  Nearby.kind = omill::FrontierWorkKind::kUnknownExecutableTarget;
  Nearby.scheduling_class =
      omill::FrontierSchedulingClass::kQuarantinedSelectorArm;
  Nearby.continuation_confidence =
      omill::ContinuationConfidence::kDeadArmSuspect;
  Nearby.continuation_liveness =
      omill::ContinuationLiveness::kQuarantined;
  Nearby.failure_reason = "quarantined_selector_arm_deferred";

  auto &NearbyEdge =
      Orchestrator.session().graph.edge_facts_by_identity[Nearby.identity];
  NearbyEdge.identity = Nearby.identity;
  NearbyEdge.owner_function = Nearby.owner_function;
  NearbyEdge.site_index = Nearby.site_index;
  NearbyEdge.site_pc = Nearby.site_pc;
  NearbyEdge.target_pc = Nearby.target_pc;
  NearbyEdge.executable_target = Nearby.executable_target;
  NearbyEdge.kind = Nearby.kind;
  NearbyEdge.scheduling_class = Nearby.scheduling_class;
  NearbyEdge.continuation_confidence = Nearby.continuation_confidence;
  NearbyEdge.continuation_liveness = Nearby.continuation_liveness;
  NearbyEdge.failure_reason = Nearby.failure_reason;
  NearbyEdge.from_output_root_closure = true;
  NearbyEdge.is_dirty = true;

  Orchestrator.session().graph.edge_facts_by_identity.emplace(Nearby.identity,
                                                              NearbyEdge);

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401120u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto It = llvm::find_if(
      Orchestrator.session().graph.edge_facts_by_identity,
      [](const auto &entry) {
        const auto &edge = entry.second;
        return edge.from_boundary_continuation && edge.boundary &&
               edge.boundary->boundary_pc == std::optional<uint64_t>(0x401120u);
      });
  ASSERT_NE(It, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(It->second.target_pc, std::optional<uint64_t>(0x401140u));
  ASSERT_TRUE(It->second.boundary.has_value());
  EXPECT_EQ(It->second.boundary->continuation_pc,
            std::optional<uint64_t>(0x401140u));
  ASSERT_TRUE(It->second.executable_target.has_value());
  ASSERT_TRUE(It->second.executable_target->effective_target_pc.has_value());
  EXPECT_EQ(*It->second.executable_target->effective_target_pc, 0x401140u);

  auto NearbyIt =
      Orchestrator.session().graph.edge_facts_by_identity.find("closure:nearby");
  ASSERT_NE(NearbyIt,
            Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(NearbyIt->second.scheduling_class,
            omill::FrontierSchedulingClass::kTrustedLive);
  EXPECT_EQ(NearbyIt->second.continuation_confidence,
            omill::ContinuationConfidence::kTrusted);
  EXPECT_EQ(NearbyIt->second.continuation_liveness,
            omill::ContinuationLiveness::kLive);
  EXPECT_TRUE(NearbyIt->second.failure_reason.empty());
}

TEST_F(DevirtualizationOrchestratorTest,
       BoundaryContinuationWorkUsesIntraOwnerEntryTransformInsteadOfVmEnterImport) {
  llvm::Module M("boundary_continuation_intra_owner_transform", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "sub_401120", M);
  (void)addLiftedFunction(M, "blk_401140");
  (void)addLiftedFunction(M, "blk_402000");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401120),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401180u;
  boundary_fact.continuation_pc = 0x401140u;
  boundary_fact.covered_entry_pc = 0x401140u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::FrontierWorkItem Seed;
  Seed.owner_function = "sub_401000";
  Seed.site_index = 0;
  Seed.site_pc = 0x401000u;
  Seed.target_pc = 0x401140u;
  Seed.identity = "boundary-continuation:test";
  Seed.boundary = boundary_fact;
  Seed.root_frontier_kind = omill::VirtualRootFrontierKind::kCall;
  Seed.kind = omill::FrontierWorkKind::kIntraOwnerContinuation;
  Seed.status = omill::FrontierWorkStatus::kPending;
  Seed.from_boundary_continuation = true;
  Seed.executable_target = omill::ExecutableTargetFact{};
  Seed.executable_target->raw_target_pc = 0x401140u;
  Seed.executable_target->effective_target_pc = 0x401140u;

  auto &SeedEdge =
      Orchestrator.session().graph.edge_facts_by_identity[Seed.identity];
  SeedEdge.identity = Seed.identity;
  SeedEdge.owner_function = Seed.owner_function;
  SeedEdge.site_index = Seed.site_index;
  SeedEdge.site_pc = Seed.site_pc;
  SeedEdge.target_pc = Seed.target_pc;
  SeedEdge.boundary = Seed.boundary;
  SeedEdge.executable_target = Seed.executable_target;
  SeedEdge.root_frontier_kind = Seed.root_frontier_kind;
  SeedEdge.kind = Seed.kind;
  SeedEdge.status = Seed.status;
  SeedEdge.from_boundary_continuation = true;
  SeedEdge.is_dirty = true;

  Orchestrator.session().graph.edge_facts_by_identity.emplace(Seed.identity,
                                                              SeedEdge);

  auto It = Orchestrator.session().graph.edge_facts_by_identity.find(
      Seed.identity);
  ASSERT_NE(It, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(It->second.kind, omill::FrontierWorkKind::kIntraOwnerContinuation);
  ASSERT_TRUE(It->second.boundary.has_value());
  EXPECT_EQ(It->second.boundary->covered_entry_pc,
            std::optional<uint64_t>(0x401140u));

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x402000u;
  };
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t pc, uint8_t *out,
                                               size_t size) {
    if (pc != 0x401140u || size < 10)
      return false;
    const uint8_t bytes[10] = {0x68, 0x25, 0x87, 0x22, 0x43,
                               0xE9, 0xB6, 0x0E, 0x00, 0x00};
    std::memcpy(out, bytes, sizeof(bytes));
    for (size_t i = sizeof(bytes); i < size; ++i)
      out[i] = 0x90;
    return true;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_TRUE(Summary.changed);
  auto Updated = llvm::find_if(
      Orchestrator.session().graph.edge_facts_by_identity,
      [](const auto &entry) {
        const auto &edge = entry.second;
        return edge.from_boundary_continuation && edge.boundary &&
               edge.boundary->boundary_pc ==
                   std::optional<uint64_t>(0x401120u);
      });
  ASSERT_NE(Updated, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(Updated->second.kind,
            omill::FrontierWorkKind::kIntraOwnerContinuation);
  EXPECT_EQ(Updated->second.target_pc, std::optional<uint64_t>(0x402000u));
  ASSERT_TRUE(Updated->second.boundary.has_value());
  ASSERT_TRUE(Updated->second.boundary->continuation_entry_transform.has_value());
  EXPECT_EQ(Updated->second.boundary->continuation_entry_transform->kind,
            omill::ContinuationEntryTransformKind::kPushImmediateJump);
  EXPECT_EQ(Updated->second.boundary->continuation_entry_transform->jump_target_pc,
            std::optional<uint64_t>(0x402000u));
  EXPECT_EQ(Updated->second.boundary->continuation_pc,
            std::optional<uint64_t>(0x402000u));
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkRedirectsNormalizedBoundaryContinuationToTrackedSeed) {
  llvm::Module M("boundary_continuation_redirects_normalized_seed", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  omill::FrontierWorkItem Seed;
  Seed.owner_function = "sub_401000";
  Seed.site_index = 0;
  Seed.site_pc = 0x401000u;
  Seed.target_pc = 0x401140u;
  Seed.identity = "closure:seed";
  Seed.executable_target = omill::ExecutableTargetFact{};
  Seed.executable_target->raw_target_pc = 0x401140u;
  Seed.executable_target->effective_target_pc = 0x401140u;
  Seed.kind = omill::FrontierWorkKind::kUnknownExecutableTarget;
  Seed.status = omill::FrontierWorkStatus::kPending;
  Seed.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;

  auto &SeedEdge =
      Orchestrator.session().graph.edge_facts_by_identity[Seed.identity];
  SeedEdge.identity = Seed.identity;
  SeedEdge.owner_function = Seed.owner_function;
  SeedEdge.site_index = Seed.site_index;
  SeedEdge.site_pc = Seed.site_pc;
  SeedEdge.target_pc = Seed.target_pc;
  SeedEdge.executable_target = Seed.executable_target;
  SeedEdge.kind = Seed.kind;
  SeedEdge.status = Seed.status;
  SeedEdge.scheduling_class = Seed.scheduling_class;
  SeedEdge.from_output_root_closure = true;
  SeedEdge.is_dirty = true;

  Orchestrator.session().graph.edge_facts_by_identity.emplace(Seed.identity,
                                                              SeedEdge);

  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401120u;
  boundary_fact.native_target_pc = 0x401120u;
  boundary_fact.continuation_pc = 0x401145u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  ASSERT_TRUE(Orchestrator.enqueueBoundaryContinuationWork(
      M, boundary_fact, "sub_401000", 0x401000u));

  auto callbacks = makeFrontierCallbacks();
  callbacks.has_defined_target = [](uint64_t pc) { return pc == 0x401140u; };
  callbacks.can_decode_target = [](uint64_t pc) { return pc == 0x401140u; };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, callbacks);

  EXPECT_TRUE(Summary.changed);
  EXPECT_GE(Summary.skipped_materialized, 1u);

  auto It = Orchestrator.session().graph.edge_facts_by_identity.find(
      "boundary-continuation:401120:401140:401120::");
  ASSERT_NE(It, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(It->second.status, omill::FrontierWorkStatus::kSkippedMaterialized);
  EXPECT_EQ(It->second.failure_reason,
            "boundary_continuation_redirected_to_nearby_seed");
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkPreservesTrustedContinuationProofForClosureSeed) {
  llvm::Module M("trusted_proof_closure_seed", Ctx);
  auto *Owner = addLiftedFunction(M, "sub_401000");
  Owner->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  omill::FrontierWorkItem Trusted;
  Trusted.owner_function = "sub_401000";
  Trusted.site_index = 0;
  Trusted.site_pc = 0x401000u;
  Trusted.target_pc = 0x401260u;
  Trusted.identity = "closure:trusted";
  Trusted.boundary = omill::BoundaryFact{};
  Trusted.boundary->boundary_pc = 0x401260u;
  Trusted.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Trusted.boundary->is_vm_enter = true;
  Trusted.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Trusted.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;

  omill::SessionEdgeFact TrustedEdge;
  TrustedEdge.identity = Trusted.identity;
  TrustedEdge.owner_function = Trusted.owner_function;
  TrustedEdge.site_index = Trusted.site_index;
  TrustedEdge.site_pc = Trusted.site_pc;
  TrustedEdge.target_pc = Trusted.target_pc;
  TrustedEdge.boundary = Trusted.boundary;
  TrustedEdge.kind = Trusted.kind;
  TrustedEdge.status = Trusted.status;
  TrustedEdge.scheduling_class = Trusted.scheduling_class;
  Orchestrator.session().graph.edge_facts_by_identity.emplace(
      Trusted.identity, std::move(TrustedEdge));

  omill::SessionEdgeFact PromotedEdge;
  PromotedEdge.identity = "closure:promoted";
  PromotedEdge.owner_function = "sub_401000";
  PromotedEdge.site_index = 1;
  PromotedEdge.site_pc = 0x401004u;
  PromotedEdge.target_pc = 0x401230u;
  PromotedEdge.kind = omill::FrontierWorkKind::kUnknownExecutableTarget;
  PromotedEdge.status = omill::FrontierWorkStatus::kPending;
  PromotedEdge.continuation_confidence =
      omill::ContinuationConfidence::kTrusted;
  PromotedEdge.continuation_liveness = omill::ContinuationLiveness::kLive;
  PromotedEdge.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;
  PromotedEdge.continuation_rationale = "boundary_reentry_nearby_seed";
  PromotedEdge.continuation_proof = omill::ContinuationProof{};
  PromotedEdge.continuation_proof->edge_identity = PromotedEdge.identity;
  PromotedEdge.continuation_proof->raw_target_pc = 0x401230u;
  PromotedEdge.continuation_proof->effective_target_pc = 0x401230u;
  PromotedEdge.continuation_proof->source_handler_name = "sub_401000";
  PromotedEdge.continuation_proof->provenance =
      omill::ContinuationProvenance::kSelectorDerived;
  PromotedEdge.continuation_proof->confidence =
      omill::ContinuationConfidence::kTrusted;
  PromotedEdge.continuation_proof->liveness =
      omill::ContinuationLiveness::kLive;
  PromotedEdge.continuation_proof->scheduling_class =
      omill::FrontierSchedulingClass::kTrustedLive;
  PromotedEdge.continuation_proof->is_trusted_entry = true;
  PromotedEdge.continuation_proof->resolution_kind =
      omill::ContinuationResolutionKind::kTrustedEntry;
  PromotedEdge.continuation_proof->import_disposition =
      omill::ContinuationImportDisposition::kRetryable;
  PromotedEdge.continuation_proof->selected_root_import_class =
      omill::ChildImportClass::kClosedSliceRoot;
  PromotedEdge.continuation_proof->rationale =
      "boundary_reentry_nearby_seed";
  Orchestrator.session().graph.edge_facts_by_identity.emplace(
      PromotedEdge.identity, PromotedEdge);

  omill::FrontierWorkItem Promoted;
  Promoted.owner_function = PromotedEdge.owner_function;
  Promoted.site_index = PromotedEdge.site_index;
  Promoted.site_pc = PromotedEdge.site_pc;
  Promoted.target_pc = PromotedEdge.target_pc;
  Promoted.identity = PromotedEdge.identity;
  Promoted.kind = PromotedEdge.kind;
  Promoted.status = PromotedEdge.status;
  Promoted.continuation_confidence = PromotedEdge.continuation_confidence;
  Promoted.continuation_liveness = PromotedEdge.continuation_liveness;
  Promoted.scheduling_class = PromotedEdge.scheduling_class;
  Promoted.continuation_rationale = PromotedEdge.continuation_rationale;


  auto Callbacks = makeFrontierCallbacks();
  Callbacks.is_executable_target = [](uint64_t) { return true; };
  Callbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x401230u;
  };
  Callbacks.can_decode_target = [](uint64_t pc) {
    return pc == 0x401230u;
  };
  Callbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 16)
      return false;
    std::memset(out, 0x90, size);
    return true;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, Callbacks);

  EXPECT_FALSE(llvm::any_of(Summary.notes, [](const std::string &note) {
    return note.find("deferred_quarantined:closure:promoted") !=
           std::string::npos;
  }));
  EXPECT_GE(Summary.skipped_materialized, 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       RequeueBoundaryEdgesForTargetInvalidatesNativeBoundaryEdge) {
  llvm::Module M("requeue_boundary_edge", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  omill::SessionEdgeFact BoundaryEdge;
  BoundaryEdge.identity = "dispatch:sub_401000:0:401700";
  BoundaryEdge.owner_function = "sub_401000";
  BoundaryEdge.site_index = 0;
  BoundaryEdge.site_pc = 0x401000u;
  BoundaryEdge.target_pc = 0x401700u;
  BoundaryEdge.kind = omill::FrontierWorkKind::kNativeCallBoundary;
  BoundaryEdge.status = omill::FrontierWorkStatus::kSkippedMaterialized;
  BoundaryEdge.scheduling_class =
      omill::FrontierSchedulingClass::kNativeOrVmEnterBoundary;
  BoundaryEdge.boundary = omill::BoundaryFact{};
  BoundaryEdge.boundary->boundary_pc = 0x401710u;
  BoundaryEdge.boundary->native_target_pc = 0x401700u;
  BoundaryEdge.boundary->continuation_pc = 0x401720u;
  BoundaryEdge.boundary->reenters_vm = true;
  BoundaryEdge.boundary->exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  BoundaryEdge.boundary->kind = omill::BoundaryKind::kNativeBoundary;
  Orchestrator.session().graph.edge_facts_by_identity.emplace(
      BoundaryEdge.identity, BoundaryEdge);

  ASSERT_TRUE(
      Orchestrator.requeueBoundaryEdgesForTarget(M, 0x401700u, "bridge_ready"));

  auto It = Orchestrator.session().graph.edge_facts_by_identity.find(
      BoundaryEdge.identity);
  ASSERT_NE(It, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(It->second.status, omill::FrontierWorkStatus::kInvalidated);
  EXPECT_EQ(It->second.failure_reason, "bridge_ready");
  EXPECT_TRUE(It->second.is_dirty);
  EXPECT_TRUE(llvm::is_contained(
      omill::collectSessionFrontierIdentities(Orchestrator.session()),
      BoundaryEdge.identity));
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesPrologueCallBoundaryAsNativeExit) {
  llvm::Module M("native_prologue_boundary_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011A0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 16)
      return false;
    const uint8_t bytes[16] = {0x48, 0x89, 0x4C, 0x24, 0x08, 0x48,
                               0x83, 0xEC, 0x38, 0xB9, 0x17, 0x00,
                               0x00, 0x00, 0xFF, 0x15};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, CallBoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_native_exit, 1u);
  auto *BoundaryDecl = M.getFunction("sub_4011a0");
  ASSERT_NE(BoundaryDecl, nullptr);
  EXPECT_TRUE(BoundaryDecl->isDeclaration());
  EXPECT_EQ(BoundaryDecl->getFnAttribute("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_exec_unknown_return");
}

TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenImportsClassifiedVmEnterViaCallbacks) {
  llvm::Module M("vm_enter_child_import", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011C0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto VmEnterCallbacks = makeFrontierCallbacks();
  VmEnterCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 32)
      return false;
    const uint8_t bytes[32] = {0x57, 0x4C, 0x89, 0xBC, 0x3C, 0x63, 0xA3, 0xFF,
                               0xFF, 0x52, 0x55, 0x50, 0x41, 0x52, 0x9C, 0x5E,
                               0x48, 0x89, 0xB4, 0x3C, 0x63, 0xA3, 0xFF, 0xFF,
                               0x66, 0x45, 0x0F, 0xBB, 0xC9, 0x48, 0x8D, 0x0C};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Round = Orchestrator.runFrontierRound(M, ProjectionLifter, VmEnterCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);
  ASSERT_FALSE(Round.crashed);
  ASSERT_TRUE(Round.changed);

  auto *Placeholder = M.getFunction("omill_vm_enter_target_4011C0");
  ASSERT_NE(Placeholder, nullptr);
  ASSERT_TRUE(Placeholder->isDeclaration());

  bool noted_target = false;
  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder,
          std::string &failure_reason,
          llvm::Function *&imported_root) -> bool {
        EXPECT_EQ(target_pc, 0x4011C0u);
        EXPECT_EQ(&placeholder, Placeholder);
        imported_root = addLiftedFunction(M, "tbrec_sub_4011c0");
        return true;
      };
  ImportCallbacks.on_imported_target = [&](uint64_t target_pc) {
    noted_target = (target_pc == 0x4011C0u);
  };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_TRUE(noted_target);
  EXPECT_TRUE(
      Orchestrator.session().attempted_vm_enter_child_import_pcs.count(0x4011C0u));
  EXPECT_EQ(M.getFunction("omill_vm_enter_target_4011C0"), nullptr);
  EXPECT_NE(M.getFunction("tbrec_sub_4011c0"), nullptr);

  auto Second = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Second.attempted, 0u);
  EXPECT_EQ(Second.imported, 0u);
  EXPECT_FALSE(Second.changed);
}

TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenReplacesDefinedModeledBoundaryPlaceholder) {
  llvm::Module M("vm_enter_import_replaces_modeled_boundary", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = addLiftedFunction(M, "sub_4011c0");

  omill::BoundaryFact placeholder_fact;
  placeholder_fact.boundary_pc = 0x4011C0u;
  placeholder_fact.native_target_pc = 0x4011C0u;
  placeholder_fact.continuation_pc = 0x4011D0u;
  placeholder_fact.reenters_vm = true;
  placeholder_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  placeholder_fact.kind = omill::BoundaryKind::kNativeBoundary;
  omill::writeBoundaryFact(*Placeholder, placeholder_fact);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Placeholder, {Root->getArg(0), B.getInt64(0x4011C0),
                                   Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["vmenter:4011c0"];
  Edge.identity = "vmenter:4011c0";
  Edge.owner_function = "sub_401000";
  Edge.target_pc = 0x4011C0u;
  Edge.boundary = omill::BoundaryFact{};
  Edge.boundary->boundary_pc = 0x4011C0u;
  Edge.boundary->is_vm_enter = true;
  Edge.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Edge.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;
  Edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
  Orchestrator.session().attempted_vm_enter_child_import_pcs.insert(0x4011C0u);

  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder,
          std::string &, llvm::Function *&imported_root) -> bool {
        EXPECT_EQ(target_pc, 0x4011C0u);
        EXPECT_EQ(&placeholder, Placeholder);
        imported_root = addLiftedFunction(M, "blk_4011c0");
        return true;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_EQ(M.getFunction("sub_4011c0"), nullptr);
  auto *Imported = M.getFunction("blk_4011c0");
  ASSERT_NE(Imported, nullptr);
  auto *Call = llvm::cast<llvm::CallBase>(Root->getEntryBlock().getTerminator()->getPrevNode());
  EXPECT_EQ(Call->getCalledFunction(), Imported);
  auto ImportedIt =
      Orchestrator.session().imported_vm_enter_child_roots.find(0x4011C0u);
  ASSERT_NE(ImportedIt, Orchestrator.session().imported_vm_enter_child_roots.end());
  EXPECT_EQ(ImportedIt->second, "blk_4011c0");
}

TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenSynthesizesMissingVmEnterPlaceholder) {
  llvm::Module M("vm_enter_import_synthesizes_placeholder", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["vmenter:4011d0"];
  Edge.identity = "vmenter:4011d0";
  Edge.owner_function = "sub_401000";
  Edge.target_pc = 0x4011D0u;
  Edge.boundary = omill::BoundaryFact{};
  Edge.boundary->boundary_pc = 0x4011D0u;
  Edge.boundary->is_vm_enter = true;
  Edge.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Edge.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;
  Edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;

  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder, std::string &,
          llvm::Function *&imported_root) -> bool {
        EXPECT_EQ(target_pc, 0x4011D0u);
        EXPECT_EQ(llvm::StringRef(placeholder.getName()).lower(),
                  "omill_vm_enter_target_4011d0");
        imported_root = addLiftedFunction(M, "blk_4011d0");
        return true;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_EQ(M.getFunction("omill_vm_enter_target_4011D0"), nullptr);
  auto *Imported = M.getFunction("blk_4011d0");
  ASSERT_NE(Imported, nullptr);
  auto ImportedIt =
      Orchestrator.session().imported_vm_enter_child_roots.find(0x4011D0u);
  ASSERT_NE(ImportedIt, Orchestrator.session().imported_vm_enter_child_roots.end());
  EXPECT_EQ(ImportedIt->second, "blk_4011d0");
}

TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenConsumesLateFrontierVmEnterSeed) {
  llvm::Module M("vm_enter_import_late_frontier_seed", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  omill::FrontierWorkItem Seed;
  Seed.owner_function = "sub_401000";
  Seed.site_index = 0;
  Seed.site_pc = 0x401000u;
  Seed.target_pc = 0x4011E0u;
  Seed.identity = "closure:late_vmenter";
  Seed.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Seed.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
  Seed.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;
  Seed.boundary = omill::BoundaryFact{};
  Seed.boundary->boundary_pc = 0x4011E0u;
  Seed.boundary->is_vm_enter = true;
  Seed.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Seed.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;

  Orchestrator.session().graph.edge_facts_by_identity.emplace(
      Seed.identity, omill::SessionEdgeFact{});
  auto &SeedGraphEdge =
      Orchestrator.session().graph.edge_facts_by_identity[Seed.identity];
  SeedGraphEdge.identity = Seed.identity;
  SeedGraphEdge.owner_function = Seed.owner_function;
  SeedGraphEdge.site_index = Seed.site_index;
  SeedGraphEdge.site_pc = Seed.site_pc;
  SeedGraphEdge.target_pc = Seed.target_pc;
  SeedGraphEdge.boundary = Seed.boundary;
  SeedGraphEdge.kind = Seed.kind;
  SeedGraphEdge.status = Seed.status;
  SeedGraphEdge.scheduling_class = Seed.scheduling_class;
  SeedGraphEdge.from_output_root_closure = true;

  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder, std::string &,
          llvm::Function *&imported_root) -> bool {
        EXPECT_EQ(target_pc, 0x4011E0u);
        EXPECT_EQ(llvm::StringRef(placeholder.getName()).lower(),
                  "omill_vm_enter_target_4011e0");
        imported_root = addLiftedFunction(M, "blk_4011e0");
        return true;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_EQ(M.getFunction("omill_vm_enter_target_4011E0"), nullptr);
  EXPECT_NE(M.getFunction("blk_4011e0"), nullptr);

  auto ImportedIt =
      Orchestrator.session().imported_vm_enter_child_roots.find(0x4011E0u);
  ASSERT_NE(ImportedIt, Orchestrator.session().imported_vm_enter_child_roots.end());
  EXPECT_EQ(ImportedIt->second, "blk_4011e0");

  auto EdgeIt = Orchestrator.session().graph.edge_facts_by_identity.find(
      "closure:late_vmenter");
  ASSERT_NE(EdgeIt, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(EdgeIt->second.target_pc, std::optional<uint64_t>(0x4011E0u));
  EXPECT_EQ(EdgeIt->second.status,
            omill::FrontierWorkStatus::kClassifiedVmEnter);
}

TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenMergesRicherClosureBoundaryMetadata) {
  llvm::Module M("vm_enter_import_merges_closure_boundary_metadata", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["vmenter:4011f8"];
  Edge.identity = "vmenter:4011f8";
  Edge.owner_function = "sub_401000";
  Edge.site_index = 0;
  Edge.site_pc = 0x401000u;
  Edge.target_pc = 0x4011F8u;
  Edge.boundary = omill::BoundaryFact{};
  Edge.boundary->boundary_pc = 0x4011F8u;
  Edge.boundary->is_vm_enter = true;
  Edge.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Edge.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;
  Edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;

  omill::FrontierWorkItem ClosureSeed;
  ClosureSeed.owner_function = "sub_401000";
  ClosureSeed.site_index = 1;
  ClosureSeed.site_pc = 0x401120u;
  ClosureSeed.target_pc = 0x4011F8u;
  ClosureSeed.identity = "closure:4011f8-rich";
  ClosureSeed.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  ClosureSeed.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
  ClosureSeed.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;
  ClosureSeed.continuation_confidence = omill::ContinuationConfidence::kTrusted;
  ClosureSeed.continuation_liveness = omill::ContinuationLiveness::kLive;
  ClosureSeed.continuation_rationale = "return_address_controlled";
  ClosureSeed.boundary = omill::BoundaryFact{};
  ClosureSeed.boundary->boundary_pc = 0x4011F8u;
  ClosureSeed.boundary->continuation_pc = 0x40120Bu;
  ClosureSeed.boundary->continuation_owner_id = 9u;
  ClosureSeed.boundary->continuation_owner_kind =
  omill::VirtualStackOwnerKind::kFramePointerLike;
  ClosureSeed.boundary->controlled_return_pc = 0x401280u;
  ClosureSeed.boundary->return_address_control_kind =
      omill::VirtualReturnAddressControlKind::kRedirectedConstant;
  ClosureSeed.boundary->covered_entry_pc = 0x4011F8u;
  ClosureSeed.boundary->continuation_entry_transform =
      omill::ContinuationEntryTransform{
          omill::ContinuationEntryTransformKind::kPushImmediateJump, 0x4011F8u,
          0x401340u, 0x1234u, true};
  ClosureSeed.boundary->is_vm_enter = true;
  ClosureSeed.boundary->reenters_vm = true;
  ClosureSeed.boundary->suppresses_normal_fallthrough = true;
  ClosureSeed.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  ClosureSeed.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;
  Orchestrator.session().graph.edge_facts_by_identity.emplace(
      ClosureSeed.identity, omill::SessionEdgeFact{});
  auto &ClosureSeedEdge =
      Orchestrator.session().graph.edge_facts_by_identity[ClosureSeed.identity];
  ClosureSeedEdge.identity = ClosureSeed.identity;
  ClosureSeedEdge.owner_function = ClosureSeed.owner_function;
  ClosureSeedEdge.site_index = ClosureSeed.site_index;
  ClosureSeedEdge.site_pc = ClosureSeed.site_pc;
  ClosureSeedEdge.target_pc = ClosureSeed.target_pc;
  ClosureSeedEdge.boundary = ClosureSeed.boundary;
  ClosureSeedEdge.kind = ClosureSeed.kind;
  ClosureSeedEdge.status = ClosureSeed.status;
  ClosureSeedEdge.scheduling_class = ClosureSeed.scheduling_class;
  ClosureSeedEdge.continuation_confidence = ClosureSeed.continuation_confidence;
  ClosureSeedEdge.continuation_liveness = ClosureSeed.continuation_liveness;
  ClosureSeedEdge.continuation_rationale = ClosureSeed.continuation_rationale;
  ClosureSeedEdge.from_output_root_closure = true;

  Orchestrator.session().graph.boundary_facts_by_target[0x4011F8u] =
      omill::SessionBoundaryFact{0x4011F8u, ClosureSeed.kind,
                                 ClosureSeed.boundary, std::nullopt, false};

  bool saw_merged_placeholder = false;
  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder, std::string &,
          llvm::Function *&imported_root) -> bool {
        EXPECT_EQ(target_pc, 0x4011F8u);
        auto fact = omill::readBoundaryFact(placeholder);
        EXPECT_TRUE(fact.has_value());
        if (!fact.has_value())
          return false;
        EXPECT_EQ(fact->continuation_pc, std::optional<uint64_t>(0x40120Bu));
        EXPECT_EQ(fact->continuation_owner_id, std::optional<unsigned>(9u));
        EXPECT_EQ(fact->continuation_owner_kind,
                  omill::VirtualStackOwnerKind::kFramePointerLike);
        EXPECT_EQ(fact->controlled_return_pc, std::optional<uint64_t>(0x401280u));
        EXPECT_EQ(fact->return_address_control_kind,
                  omill::VirtualReturnAddressControlKind::kRedirectedConstant);
        EXPECT_TRUE(fact->continuation_entry_transform.has_value());
        if (!fact->continuation_entry_transform.has_value())
          return false;
        EXPECT_EQ(fact->continuation_entry_transform->jump_target_pc,
                  std::optional<uint64_t>(0x401340u));
        EXPECT_TRUE(fact->suppresses_normal_fallthrough);
        saw_merged_placeholder = true;
        imported_root = addLiftedFunction(M, "blk_4011f8");
        return true;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_TRUE(saw_merged_placeholder);

  auto EdgeIt = llvm::find_if(
      Orchestrator.session().graph.edge_facts_by_identity,
      [](const auto &entry) {
        const auto &edge = entry.second;
        return edge.target_pc == std::optional<uint64_t>(0x4011F8u) &&
               edge.kind == omill::FrontierWorkKind::kVmEnterBoundary;
      });
  ASSERT_NE(EdgeIt, Orchestrator.session().graph.edge_facts_by_identity.end());
  ASSERT_TRUE(EdgeIt->second.boundary.has_value());
  EXPECT_EQ(EdgeIt->second.boundary->continuation_owner_id,
            std::optional<unsigned>(9u));
  EXPECT_EQ(EdgeIt->second.boundary->controlled_return_pc,
            std::optional<uint64_t>(0x401280u));
  EXPECT_TRUE(EdgeIt->second.boundary->continuation_entry_transform.has_value());
  EXPECT_EQ(EdgeIt->second.status,
            omill::FrontierWorkStatus::kClassifiedVmEnter);
}


TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenUsesRelatedBoundaryEvidenceForTarget) {
  llvm::Module M("vm_enter_import_uses_related_boundary_evidence", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  auto &VmEnterEdge =
      Orchestrator.session().graph.edge_facts_by_identity["vmenter:401208"];
  VmEnterEdge.identity = "vmenter:401208";
  VmEnterEdge.owner_function = "sub_401000";
  VmEnterEdge.site_index = 0;
  VmEnterEdge.site_pc = 0x401000u;
  VmEnterEdge.target_pc = 0x401208u;
  VmEnterEdge.kind = omill::FrontierWorkKind::kUnknownExecutableTarget;
  VmEnterEdge.status = omill::FrontierWorkStatus::kPending;

  auto &BoundaryEntry =
      Orchestrator.session().graph.boundary_facts_by_target[0x401150u];
  BoundaryEntry.target_pc = 0x401150u;
  BoundaryEntry.kind = omill::FrontierWorkKind::kNativeCallBoundary;
  BoundaryEntry.boundary = omill::BoundaryFact{};
  BoundaryEntry.boundary->boundary_pc = 0x401208u;
  BoundaryEntry.boundary->native_target_pc = 0x401150u;
  BoundaryEntry.boundary->continuation_pc = 0x40121Bu;
  BoundaryEntry.boundary->continuation_owner_id = 11u;
  BoundaryEntry.boundary->continuation_owner_kind =
      omill::VirtualStackOwnerKind::kFramePointerLike;
  BoundaryEntry.boundary->controlled_return_pc = 0x4012A0u;
  BoundaryEntry.boundary->return_address_control_kind =
      omill::VirtualReturnAddressControlKind::kRedirectedConstant;
  BoundaryEntry.boundary->suppresses_normal_fallthrough = true;
  BoundaryEntry.boundary->reenters_vm = true;
  BoundaryEntry.boundary->is_vm_enter = true;
  BoundaryEntry.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  BoundaryEntry.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;
  BoundaryEntry.is_dirty = false;

  bool saw_related_boundary = false;
  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder, std::string &,
          llvm::Function *&imported_root) -> bool {
        EXPECT_EQ(target_pc, 0x401208u);
        auto fact = omill::readBoundaryFact(placeholder);
        EXPECT_TRUE(fact.has_value());
        if (!fact.has_value())
          return false;
        EXPECT_EQ(fact->continuation_owner_id, std::optional<unsigned>(11u));
        EXPECT_EQ(fact->controlled_return_pc, std::optional<uint64_t>(0x4012A0u));
        EXPECT_EQ(fact->return_address_control_kind,
                  omill::VirtualReturnAddressControlKind::kRedirectedConstant);
        EXPECT_TRUE(fact->suppresses_normal_fallthrough);
        saw_related_boundary = true;
        imported_root = addLiftedFunction(M, "blk_401208");
        return true;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_TRUE(saw_related_boundary);

  auto EdgeIt =
      Orchestrator.session().graph.edge_facts_by_identity.find("vmenter:401208");
  ASSERT_NE(EdgeIt, Orchestrator.session().graph.edge_facts_by_identity.end());
  ASSERT_TRUE(EdgeIt->second.boundary.has_value());
  EXPECT_EQ(EdgeIt->second.boundary->continuation_owner_id,
            std::optional<unsigned>(11u));
  EXPECT_EQ(EdgeIt->second.boundary->controlled_return_pc,
            std::optional<uint64_t>(0x4012A0u));
  EXPECT_EQ(EdgeIt->second.kind, omill::FrontierWorkKind::kVmEnterBoundary);
  EXPECT_EQ(EdgeIt->second.status,
            omill::FrontierWorkStatus::kClassifiedVmEnter);
}


TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenPersistsFailureReasonOnSessionEdge) {
  llvm::Module M("vm_enter_import_failure_reason", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["vmenter:4011f0"];
  Edge.identity = "vmenter:4011f0";
  Edge.owner_function = "sub_401000";
  Edge.target_pc = 0x4011F0u;
  Edge.boundary = omill::BoundaryFact{};
  Edge.boundary->boundary_pc = 0x4011F0u;
  Edge.boundary->is_vm_enter = true;
  Edge.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Edge.boundary->kind = omill::BoundaryKind::kVmEnterBoundary;
  Edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;

  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &, std::string &failure_reason,
          llvm::Function *&) -> bool {
        EXPECT_EQ(target_pc, 0x4011F0u);
        failure_reason =
            "runtime_leak:remill_function_call+unresolved_dispatch_intrinsics";
        return false;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.attempted, 1u);
  EXPECT_EQ(Summary.imported, 0u);
  EXPECT_FALSE(Summary.changed);
  auto It =
      Orchestrator.session().graph.edge_facts_by_identity.find("vmenter:4011f0");
  ASSERT_NE(It,
            Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(
      It->second.failure_reason,
      "runtime_leak:remill_function_call+unresolved_dispatch_intrinsics");
}

TEST_F(DevirtualizationOrchestratorTest,
       RunFrontierIterationsOwnsVmEnterImportLoopViaCallbacks) {
  llvm::Module M("vm_enter_iteration_callbacks", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011C0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto VmEnterCallbacks = makeFrontierCallbacks();
  VmEnterCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 16)
      return false;
    const uint8_t bytes[16] = {0x9C, 0x50, 0x51, 0x52, 0x53, 0x54,
                               0x55, 0x56, 0x57, 0x90, 0x90, 0x90,
                               0x90, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  VmEnterCallbacks.can_decode_target = [](uint64_t) { return true; };

  unsigned before_calls = 0;
  unsigned after_calls = 0;
  unsigned imported_notes = 0;
  omill::FrontierIterationCallbacks IterationCallbacks;
  IterationCallbacks.before_frontier_round = [&](unsigned round) {
    ++before_calls;
    return round == 0;
  };
  IterationCallbacks.after_frontier_round =
      [&](unsigned, const omill::FrontierRoundSummary &,
          const omill::VmEnterChildImportSummary &import_summary) {
        ++after_calls;
        return import_summary.changed;
      };

  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.max_imports = 1;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder,
          std::string &failure_reason,
          llvm::Function *&imported_root) -> bool {
        (void)failure_reason;
        imported_root = llvm::Function::Create(
            placeholder.getFunctionType(), llvm::Function::ExternalLinkage,
            "tbrec_sub_4011c0", M);
        auto *Block =
            llvm::BasicBlock::Create(Ctx, "entry", imported_root);
        llvm::IRBuilder<> IB(Block);
        IB.CreateRet(imported_root->getArg(2));
        return target_pc == 0x4011C0;
      };
  ImportCallbacks.on_imported_target = [&](uint64_t target_pc) {
    EXPECT_EQ(target_pc, 0x4011C0u);
    ++imported_notes;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.runFrontierIterations(M, ProjectionLifter, VmEnterCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure, 3, IterationCallbacks, &ImportCallbacks);

  EXPECT_FALSE(Summary.crashed);
  EXPECT_EQ(Summary.rounds_run, 1u);
  EXPECT_EQ(Summary.vm_enter_children_imported, 1u);
  EXPECT_TRUE(Summary.changed);
  EXPECT_EQ(before_calls, 2u);
  EXPECT_EQ(after_calls, 1u);
  EXPECT_EQ(imported_notes, 1u);
  EXPECT_NE(M.getFunction("tbrec_sub_4011c0"), nullptr);
}

TEST_F(DevirtualizationOrchestratorTest,
       BuildExecutionPlanProjectsPersistentSessionGraphState) {
  llvm::Module M("session_graph_projection", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x401120), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  const auto &Session = Orchestrator.session();
  auto HandlerIt = Session.graph.handler_nodes.find("sub_401000");
  ASSERT_NE(HandlerIt, Session.graph.handler_nodes.end());
  EXPECT_TRUE(HandlerIt->second.is_output_root);
  EXPECT_TRUE(HandlerIt->second.entry_va.has_value());
  EXPECT_EQ(*HandlerIt->second.entry_va, 0x401000u);

  auto RootSliceIt = Session.graph.root_slices_by_va.find(0x401000u);
  ASSERT_NE(RootSliceIt, Session.graph.root_slices_by_va.end());
  EXPECT_EQ(RootSliceIt->second.root_function, "sub_401000");
  ASSERT_EQ(RootSliceIt->second.frontier_edge_identities.size(), 1u);

  const auto &EdgeId = RootSliceIt->second.frontier_edge_identities.front();
  auto EdgeIt = Session.graph.edge_facts_by_identity.find(EdgeId);
  ASSERT_NE(EdgeIt, Session.graph.edge_facts_by_identity.end());
  EXPECT_TRUE(EdgeIt->second.target_pc.has_value());
  EXPECT_EQ(*EdgeIt->second.target_pc, 0x401120u);

  auto FrontierItems = omill::collectSessionFrontierWorkItems(Session);
  auto CompatIt = std::find_if(FrontierItems.begin(), FrontierItems.end(),
                               [&](const omill::FrontierWorkItem &item) {
                                 return item.identity == EdgeId;
                               });
  ASSERT_NE(CompatIt, FrontierItems.end());
  EXPECT_TRUE(CompatIt->target_pc.has_value());
  EXPECT_EQ(*CompatIt->target_pc, 0x401120u);
}

TEST_F(DevirtualizationOrchestratorTest,
       BuildExecutionPlanRefreshesOnlyDirtyHandlerNodesAfterInitialProjection) {
  llvm::Module M("session_graph_incremental_refresh", Ctx);
  auto *RootA = addLiftedFunction(M, "sub_401000");
  RootA->addFnAttr("omill.output_root");
  auto *RootB = addLiftedFunction(M, "sub_401100");
  RootB->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto &Session = const_cast<omill::DevirtualizationSession &>(Orchestrator.session());
  auto HandlerIt = Session.graph.handler_nodes.find("sub_401100");
  ASSERT_NE(HandlerIt, Session.graph.handler_nodes.end());
  ASSERT_TRUE(HandlerIt->second.local_summary.has_value());
  HandlerIt->second.local_summary->direct_callees = {"sentinel_helper"};

  RootA->addFnAttr("omill.vm_newly_lifted");
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto HandlerItAfter = Orchestrator.session().graph.handler_nodes.find("sub_401100");
  ASSERT_NE(HandlerItAfter, Orchestrator.session().graph.handler_nodes.end());
  ASSERT_TRUE(HandlerItAfter->second.local_summary.has_value());
  ASSERT_EQ(HandlerItAfter->second.local_summary->direct_callees.size(), 1u);
  EXPECT_EQ(HandlerItAfter->second.local_summary->direct_callees.front(),
            "sentinel_helper");
}

TEST_F(DevirtualizationOrchestratorTest,
       BuildExecutionPlanRefreshesOnlyDirtyDerivedRootSlicesAfterInitialProjection) {
  llvm::Module M("session_graph_incremental_root_slices", Ctx);
  auto *RootA = addLiftedFunction(M, "sub_401000");
  RootA->addFnAttr("omill.output_root");
  auto *RootB = addLiftedFunction(M, "sub_401100");
  RootB->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto &Session = const_cast<omill::DevirtualizationSession &>(Orchestrator.session());
  auto RootSliceIt = Session.graph.root_slices_by_va.find(0x401100u);
  ASSERT_NE(RootSliceIt, Session.graph.root_slices_by_va.end());
  RootSliceIt->second.frontier_edge_identities = {"sentinel_edge"};
  RootSliceIt->second.reachable_handler_names = {"sub_401100"};

  RootA->addFnAttr("omill.vm_newly_lifted");
  (void)Orchestrator.buildExecutionPlan(M, Request);

  EXPECT_EQ(Orchestrator.session().graph.dirty_root_vas.count(0x401100u), 0u);
  auto RootSliceItAfter =
      Orchestrator.session().graph.root_slices_by_va.find(0x401100u);
  ASSERT_NE(RootSliceItAfter,
            Orchestrator.session().graph.root_slices_by_va.end());
  ASSERT_EQ(RootSliceItAfter->second.frontier_edge_identities.size(), 1u);
  EXPECT_EQ(RootSliceItAfter->second.frontier_edge_identities.front(),
            "sentinel_edge");
}

TEST_F(DevirtualizationOrchestratorTest,
       RefreshSessionStateReportsIncrementalSessionGraphTelemetry) {
  llvm::Module M("session_graph_round_telemetry", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011C0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto &Session =
      const_cast<omill::DevirtualizationSession &>(Orchestrator.session());
  ASSERT_FALSE(Session.graph.edge_facts_by_identity.empty());
  auto EdgeIt = Session.graph.edge_facts_by_identity.begin();
  EdgeIt->second.kind = omill::FrontierWorkKind::kNativeCallBoundary;
  EdgeIt->second.boundary = omill::BoundaryFact{};
  EdgeIt->second.boundary->exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeExecUnknownReturn;
  auto *NoopTy = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
  auto *Noop = llvm::Function::Create(NoopTy, llvm::Function::ExternalLinkage,
                                      "noop_telemetry", M);
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> DirtyB(&Entry);
  DirtyB.CreateCall(Jump, {Root->getArg(0), DirtyB.getInt64(0x4011C0),
                           Root->getArg(2)});
  DirtyB.CreateCall(Noop);
  DirtyB.CreateRet(Root->getArg(2));

  (void)Orchestrator.buildExecutionPlan(M, Request);

  EXPECT_GE(Orchestrator.session().latest_round.dirty_handler_nodes, 1u);
  EXPECT_GE(Orchestrator.session().latest_round.dirty_edge_facts, 1u);
  EXPECT_EQ(Orchestrator.session().latest_round.dirty_boundary_facts, 1u);
  EXPECT_GE(Orchestrator.session().latest_round.dirty_root_slices, 1u);
  EXPECT_GE(Orchestrator.session().latest_round.rebuilt_root_slices, 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       ImportNestedVmEnterChildrenUpdatesPersistentSessionRegionNode) {
  llvm::Module M("session_graph_nested_region", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011C0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto VmEnterCallbacks = makeFrontierCallbacks();
  VmEnterCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 16)
      return false;
    const uint8_t bytes[16] = {0x9C, 0x50, 0x51, 0x52, 0x53, 0x54,
                               0x55, 0x56, 0x57, 0x90, 0x90, 0x90,
                               0x90, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  VmEnterCallbacks.can_decode_target = [](uint64_t) { return true; };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Round = Orchestrator.runFrontierRound(M, ProjectionLifter, VmEnterCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);
  ASSERT_FALSE(Round.crashed);

  omill::VmEnterChildImportCallbacks ImportCallbacks;
  ImportCallbacks.enabled = true;
  ImportCallbacks.try_import_target =
      [&](uint64_t target_pc, llvm::Function &placeholder,
          std::string &failure_reason,
          llvm::Function *&imported_root) -> bool {
        (void)failure_reason;
        EXPECT_EQ(target_pc, 0x4011C0u);
        imported_root = llvm::Function::Create(
            placeholder.getFunctionType(), llvm::Function::ExternalLinkage,
            "tbrec_sub_4011c0", M);
        auto *Block = llvm::BasicBlock::Create(Ctx, "entry", imported_root);
        llvm::IRBuilder<> IB(Block);
        IB.CreateRet(imported_root->getArg(2));
        return true;
      };

  auto Summary = Orchestrator.importNestedVmEnterChildren(M, ImportCallbacks);
  EXPECT_EQ(Summary.imported, 1u);

  const auto &Session = Orchestrator.session();
  auto RegionIt = Session.graph.region_nodes_by_entry_pc.find(0x4011C0u);
  ASSERT_NE(RegionIt, Session.graph.region_nodes_by_entry_pc.end());
  EXPECT_EQ(RegionIt->second.kind, omill::SessionRegionKind::kNestedVmEnter);
  EXPECT_EQ(RegionIt->second.status, omill::SessionRegionStatus::kImported);
  ASSERT_TRUE(RegionIt->second.imported_root_function.has_value());
  EXPECT_EQ(*RegionIt->second.imported_root_function, "tbrec_sub_4011c0");
  EXPECT_FALSE(RegionIt->second.frontier_edge_identities.empty());

  bool saw_vm_enter_edge = false;
  for (const auto &edge_id : RegionIt->second.frontier_edge_identities) {
    auto EdgeIt = Session.graph.edge_facts_by_identity.find(edge_id);
    ASSERT_NE(EdgeIt, Session.graph.edge_facts_by_identity.end());
    if (EdgeIt->second.target_pc && *EdgeIt->second.target_pc == 0x4011C0u &&
        EdgeIt->second.status == omill::FrontierWorkStatus::kClassifiedVmEnter) {
      saw_vm_enter_edge = true;
    }
  }
  EXPECT_TRUE(saw_vm_enter_edge);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkKeepsDecodableStackHeavyTargetLiftableWithoutEarlyCall) {
  llvm::Module M("stack_heavy_decodable_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Target = addLiftedFunction(M, "blk_4011c0");
  Target->addFnAttr("omill.closed_root_slice", "1");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011C0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 32)
      return false;
    const uint8_t bytes[32] = {0x57, 0x52, 0x55, 0x50, 0x41, 0x52, 0x9C, 0x5E,
                               0x48, 0x89, 0xB4, 0x3C, 0x63, 0xA3, 0xFF, 0xFF,
                               0x66, 0x45, 0x0F, 0xBB, 0xC9, 0x48, 0x8D, 0x0C,
                               0xBD, 0x82, 0x19, 0x32, 0xE7, 0x41, 0x8B, 0xF2};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };
  CallBoundaryCallbacks.has_defined_target = [](uint64_t pc) {
    return pc == 0x4011C0u;
  };

  (void)Orchestrator.discoverFrontierWork(
      M, CallBoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_EQ(Summary.classified_native_exit, 0u);
  auto FrontierItems =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto It = std::find_if(FrontierItems.begin(), FrontierItems.end(),
                         [](const omill::FrontierWorkItem &item) {
                           return item.target_pc && *item.target_pc == 0x4011C0u;
                         });
  ASSERT_NE(It, FrontierItems.end());
  EXPECT_EQ(It->kind, omill::FrontierWorkKind::kLiftableBlock);
  EXPECT_EQ(It->status, omill::FrontierWorkStatus::kSkippedMaterialized);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkDefersClosureLiftableBlocksInRecoveryMode) {
  ScopedTestEnvVar recovery_mode("OMILL_TERMINAL_BOUNDARY_RECOVERY", "1");
  llvm::Module M("recovery_closure_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x401220), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto Callbacks = makeFrontierCallbacks();
  Callbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 16)
      return false;
    const uint8_t bytes[16] = {0x48, 0x89, 0xC8, 0x48, 0x83, 0xC0, 0x08, 0x90,
                               0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  Callbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, Callbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, Callbacks);

  EXPECT_GE(Summary.failed_lift, 1u);
  EXPECT_EQ(M.getFunction("sub_401220"), nullptr);
  EXPECT_EQ(M.getFunction("blk_401220"), nullptr);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkDefersQuarantinedSelectorArmUntilTrustedWorkStalls) {
  llvm::Module M("quarantined_selector_arm", Ctx);
  auto *Owner = addLiftedFunction(M, "sub_401000");
  Owner->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());

  omill::FrontierWorkItem Trusted;
  Trusted.owner_function = "sub_401000";
  Trusted.site_index = 0;
  Trusted.site_pc = 0x401000u;
  Trusted.target_pc = 0x401260u;
  Trusted.identity = "closure:trusted";
  Trusted.boundary = omill::BoundaryFact{};
  Trusted.boundary->boundary_pc = 0x401260u;
  Trusted.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Trusted.boundary->is_vm_enter = true;
  Trusted.kind = omill::FrontierWorkKind::kVmEnterBoundary;
  Trusted.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;

  omill::FrontierWorkItem Quarantined;
  Quarantined.owner_function = "sub_401000";
  Quarantined.site_index = 0;
  Quarantined.site_pc = 0x401000u;
  Quarantined.target_pc = 0x401230u;
  Quarantined.identity = "closure:quarantined";
  Quarantined.executable_target = omill::ExecutableTargetFact{};
  Quarantined.executable_target->raw_target_pc = 0x401230u;
  Quarantined.executable_target->invalidated_executable_entry = true;
  Quarantined.kind = omill::FrontierWorkKind::kUnknownExecutableTarget;
  Quarantined.scheduling_class =
      omill::FrontierSchedulingClass::kQuarantinedSelectorArm;
  Quarantined.continuation_confidence =
      omill::ContinuationConfidence::kDeadArmSuspect;
  Quarantined.continuation_liveness =
      omill::ContinuationLiveness::kQuarantined;

  auto &TrustedEdge =
      Orchestrator.session().graph.edge_facts_by_identity[Trusted.identity];
  TrustedEdge.identity = Trusted.identity;
  TrustedEdge.owner_function = Trusted.owner_function;
  TrustedEdge.site_index = Trusted.site_index;
  TrustedEdge.site_pc = Trusted.site_pc;
  TrustedEdge.target_pc = Trusted.target_pc;
  TrustedEdge.boundary = Trusted.boundary;
  TrustedEdge.kind = Trusted.kind;
  TrustedEdge.status = Trusted.status;
  TrustedEdge.scheduling_class = Trusted.scheduling_class;

  auto &QuarantinedEdge =
      Orchestrator.session().graph.edge_facts_by_identity[Quarantined.identity];
  QuarantinedEdge.identity = Quarantined.identity;
  QuarantinedEdge.owner_function = Quarantined.owner_function;
  QuarantinedEdge.site_index = Quarantined.site_index;
  QuarantinedEdge.site_pc = Quarantined.site_pc;
  QuarantinedEdge.target_pc = Quarantined.target_pc;
  QuarantinedEdge.executable_target = Quarantined.executable_target;
  QuarantinedEdge.kind = Quarantined.kind;
  QuarantinedEdge.status = Quarantined.status;
  QuarantinedEdge.scheduling_class = Quarantined.scheduling_class;
  QuarantinedEdge.continuation_confidence =
      Quarantined.continuation_confidence;
  QuarantinedEdge.continuation_liveness =
      Quarantined.continuation_liveness;


  auto Callbacks = makeFrontierCallbacks();
  Callbacks.read_target_bytes = [](uint64_t target, uint8_t *out, size_t size) {
    if (size < 16)
      return false;
    if (target == 0x401260u) {
      const uint8_t bytes[16] = {0x9C, 0x50, 0x51, 0x52, 0x53, 0x54,
                                 0x55, 0x56, 0x57, 0x90, 0x90, 0x90,
                                 0x90, 0x90, 0x90, 0x90};
      std::memcpy(out, bytes, sizeof(bytes));
      return true;
    }
    const uint8_t bytes[16] = {0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
                               0x90, 0x90, 0x90, 0x90, 0x90, 0x90,
                               0x90, 0x90, 0x90, 0x90};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, Callbacks);

  EXPECT_TRUE(llvm::any_of(Summary.notes, [](const std::string &note) {
    return note.find("deferred_quarantined:closure:quarantined") !=
           std::string::npos;
  }));
  auto It =
      Orchestrator.session().graph.edge_facts_by_identity.find("closure:quarantined");
  ASSERT_NE(It, Orchestrator.session().graph.edge_facts_by_identity.end());
  EXPECT_EQ(It->second.status, omill::FrontierWorkStatus::kPending);
  EXPECT_EQ(It->second.failure_reason, "quarantined_selector_arm_deferred");
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesPushfqVmStyleTargetAsVmEnterBoundary) {
  llvm::Module M("vm_enter_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::GlobalValue::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4011c0), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto VmEnterCallbacks = makeFrontierCallbacks();
  VmEnterCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 32)
      return false;
    const uint8_t bytes[32] = {0x57, 0x4C, 0x89, 0xBC, 0x3C, 0x63, 0xA3, 0xFF,
                               0xFF, 0x52, 0x55, 0x50, 0x41, 0x52, 0x9C, 0x5E,
                               0x48, 0x89, 0xB4, 0x3C, 0x63, 0xA3, 0xFF, 0xFF,
                               0x66, 0x45, 0x0F, 0xBB, 0xC9, 0x48, 0x8D, 0x0C};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  VmEnterCallbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, VmEnterCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, VmEnterCallbacks);

  EXPECT_GE(Summary.classified_vm_enter, 1u);
  auto *VmEnterDecl = M.getFunction("omill_vm_enter_target_4011C0");
  ASSERT_NE(VmEnterDecl, nullptr);
  auto BoundaryFact = omill::readBoundaryFact(*VmEnterDecl);
  ASSERT_TRUE(BoundaryFact.has_value());
  EXPECT_EQ(omill::virtualExitDispositionFromBoundaryDisposition(
                BoundaryFact->exit_disposition),
            omill::VirtualExitDisposition::kVmEnter);
  EXPECT_EQ(VmEnterDecl->getFnAttribute("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_enter");
  EXPECT_TRUE(VmEnterDecl->hasFnAttribute("omill.vm_enter_target_pc"));
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesLateCallPushfqWrapperAsNativeBoundary) {
  llvm::Module M("late_call_pushfq_native_boundary", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4017f1), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto BoundaryCallbacks = makeFrontierCallbacks();
  BoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 66)
      return false;
    const uint8_t bytes[66] = {
        0x41, 0x56, 0x9C, 0x49, 0xBE, 0xB4, 0xBB, 0x0F, 0x93, 0x88, 0xC0,
        0xBA, 0x3F, 0x49, 0x8B, 0xFE, 0x41, 0xBE, 0x17, 0x32, 0x1F, 0x49,
        0x41, 0x81, 0xEE, 0x97, 0xF3, 0x24, 0xDF, 0x66, 0x44, 0x85, 0xF7,
        0x48, 0x8B, 0x7C, 0x24, 0x18, 0x48, 0xC7, 0x44, 0x24, 0x18, 0x1B,
        0xF8, 0xDB, 0xC4, 0x4E, 0x8B, 0xB4, 0x34, 0x88, 0xC1, 0x05, 0x96,
        0x9D, 0x48, 0x8D, 0x64, 0x24, 0x10, 0xE8, 0xCA, 0xAB, 0x02, 0x00};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  BoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, BoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, BoundaryCallbacks);

  EXPECT_GE(Summary.classified_native_exit, 1u);
  auto *BoundaryDecl = M.getFunction("sub_4017f1");
  ASSERT_NE(BoundaryDecl, nullptr);
  auto BoundaryFact = omill::readBoundaryFact(*BoundaryDecl);
  ASSERT_TRUE(BoundaryFact.has_value());
  EXPECT_EQ(omill::virtualExitDispositionFromBoundaryDisposition(
                BoundaryFact->exit_disposition),
            omill::VirtualExitDisposition::kVmExitNativeExecUnknownReturn);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesEpilogueSnippetAsTerminalBoundary) {
  llvm::Module M("terminal_epilogue_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x401260), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 16)
      return false;
    const uint8_t bytes[16] = {0x48, 0x81, 0xC4, 0xA8, 0x00, 0x00, 0x00, 0x41,
                               0x5D, 0x41, 0x5C, 0x5F, 0x5E, 0x5B, 0x5D, 0xC3};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, CallBoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_terminal, 1u);
  EXPECT_EQ(Summary.classified_terminal, 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesMissingBlockClosureTargetAsTerminalBoundary) {
  llvm::Module M("missing_block_closure_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *MissingBlock = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx),
                              {llvm::Type::getInt64Ty(Ctx)}, false),
      llvm::Function::ExternalLinkage, "__omill_missing_block_handler", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(MissingBlock, {B.getInt64(0x4012A0)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto Callbacks = makeFrontierCallbacks();
  auto DiscoverSummary = Orchestrator.discoverFrontierWork(
      M, Callbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  EXPECT_GE(DiscoverSummary.discovered, 1u);
  const auto FrontierItems =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto PendingIt = std::find_if(
      FrontierItems.begin(), FrontierItems.end(),
      [](const omill::FrontierWorkItem &item) {
        return item.target_pc && *item.target_pc == 0x4012A0u &&
               item.identity.find("closure:") == 0;
      });
  ASSERT_NE(PendingIt, FrontierItems.end());
  ASSERT_TRUE(PendingIt->boundary.has_value());
  EXPECT_EQ(omill::virtualExitDispositionFromBoundaryDisposition(
                PendingIt->boundary->exit_disposition),
            omill::VirtualExitDisposition::kVmExitTerminal);
  EXPECT_EQ(PendingIt->status, omill::FrontierWorkStatus::kPending);

  auto *FakeLifter =
      reinterpret_cast<omill::RemillProjectionLifter *>(static_cast<uintptr_t>(0x1));
  auto AdvanceSummary = Orchestrator.advanceFrontierWork(M, *FakeLifter, Callbacks);

  EXPECT_GE(AdvanceSummary.classified_terminal, 1u);
  auto FrontierItemsAfter =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto It = std::find_if(FrontierItemsAfter.begin(), FrontierItemsAfter.end(),
                         [](const omill::FrontierWorkItem &item) {
                           return item.target_pc && *item.target_pc == 0x4012A0u;
                         });
  ASSERT_NE(It, FrontierItemsAfter.end());
  EXPECT_EQ(It->kind, omill::FrontierWorkKind::kTerminalBoundary);
  ASSERT_TRUE(It->boundary.has_value());
  EXPECT_EQ(omill::virtualExitDispositionFromBoundaryDisposition(
                It->boundary->exit_disposition),
            omill::VirtualExitDisposition::kVmExitTerminal);
  EXPECT_EQ(It->status, omill::FrontierWorkStatus::kClassifiedTerminal);
  EXPECT_EQ(It->failure_reason, "non_liftable_terminal_boundary");
}

TEST_F(
    DevirtualizationOrchestratorTest,
    AdvanceFrontierWorkMaterializesInvalidatedExecutableMissingBlockAsPlaceholder) {
  llvm::Module M("invalidated_missing_block_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *MissingBlock = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx),
                              {llvm::Type::getInt64Ty(Ctx)}, false),
      llvm::Function::ExternalLinkage, "__omill_missing_block_handler", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  auto *call = B.CreateCall(MissingBlock, {B.getInt64(0x4012A0)});
  call->setMetadata(
      "omill.invalidated_executable_entry",
      llvm::MDTuple::get(
          Ctx, {llvm::ConstantAsMetadata::get(
                    llvm::ConstantInt::get(llvm::Type::getInt1Ty(Ctx), 1))}));
  call->setMetadata(
      "omill.invalidated_entry_source_pc",
      llvm::MDTuple::get(
          Ctx, {llvm::ConstantAsMetadata::get(B.getInt64(0x4012A0))}));
  call->setMetadata(
      "omill.invalidated_entry_failed_pc",
      llvm::MDTuple::get(
          Ctx, {llvm::ConstantAsMetadata::get(B.getInt64(0x4012AA))}));
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto Callbacks = makeFrontierCallbacks();
  Callbacks.can_decode_target = [](uint64_t) { return true; };
  auto DiscoverSummary = Orchestrator.discoverFrontierWork(
      M, Callbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  EXPECT_GE(DiscoverSummary.discovered, 1u);
  const auto FrontierItems =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto PendingIt = std::find_if(
      FrontierItems.begin(), FrontierItems.end(),
      [](const omill::FrontierWorkItem &item) {
        return item.target_pc && *item.target_pc == 0x4012A0u &&
               item.executable_target &&
               item.executable_target->invalidated_executable_entry;
      });
  ASSERT_NE(PendingIt, FrontierItems.end());
  ASSERT_TRUE(PendingIt->executable_target.has_value());
  ASSERT_TRUE(PendingIt->executable_target->invalidated_entry_source_pc.has_value());
  ASSERT_TRUE(PendingIt->executable_target->invalidated_entry_failed_pc.has_value());
  EXPECT_EQ(*PendingIt->executable_target->invalidated_entry_source_pc, 0x4012A0u);
  EXPECT_EQ(*PendingIt->executable_target->invalidated_entry_failed_pc, 0x4012AAu);

  auto *FakeLifter =
      reinterpret_cast<omill::RemillProjectionLifter *>(static_cast<uintptr_t>(0x1));
  auto AdvanceSummary = Orchestrator.advanceFrontierWork(M, *FakeLifter, Callbacks);

  EXPECT_GE(AdvanceSummary.skipped_materialized, 1u);
  auto FrontierItemsAfter =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto It = std::find_if(FrontierItemsAfter.begin(), FrontierItemsAfter.end(),
                         [](const omill::FrontierWorkItem &item) {
                           return item.target_pc && *item.target_pc == 0x4012A0u;
                         });
  ASSERT_NE(It, FrontierItemsAfter.end());
  ASSERT_TRUE(It->executable_target.has_value());
  EXPECT_TRUE(It->executable_target->invalidated_executable_entry);
  EXPECT_EQ(It->kind, omill::FrontierWorkKind::kUnknownExecutableTarget);
  EXPECT_EQ(It->status,
            omill::FrontierWorkStatus::kSkippedMaterialized);

  llvm::Function *placeholder = nullptr;
  for (auto &F : M) {
    if (!F.getName().contains_insensitive("4012a0"))
      continue;
    placeholder = &F;
    break;
  }
  ASSERT_NE(placeholder, nullptr);
  auto placeholder_fact = omill::readExecutableTargetFact(*placeholder);
  ASSERT_TRUE(placeholder_fact.has_value());
  EXPECT_TRUE(placeholder_fact->invalidated_executable_entry);
  ASSERT_TRUE(placeholder_fact->invalidated_entry_source_pc.has_value());
  ASSERT_TRUE(placeholder_fact->invalidated_entry_failed_pc.has_value());
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkClassifiesJunkExecutableSnippetAsTerminalBoundary) {
  llvm::Module M("terminal_junk_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x4012cf), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto CallBoundaryCallbacks = makeFrontierCallbacks();
  CallBoundaryCallbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                               size_t size) {
    if (size < 16)
      return false;
    const uint8_t bytes[16] = {0x59, 0xEE, 0xF9, 0x60, 0x93, 0xFC,
                               0x5C, 0xAD, 0xB3, 0xAD, 0x3D, 0x20,
                               0x67, 0x46, 0xAD, 0xB3};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  CallBoundaryCallbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, CallBoundaryCallbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_terminal, 1u);
  EXPECT_EQ(Summary.classified_terminal, 1u);
}

TEST_F(DevirtualizationOrchestratorTest,
       AdvanceFrontierWorkMaterializesNonEntryExecutableSnippetPlaceholder) {
  llvm::Module M("exec_snippet_frontier", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Jump = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__remill_jump", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Jump, {Root->getArg(0), B.getInt64(0x401280), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRequest Request;
  Request.root_vas.push_back(0x401000);
  (void)Orchestrator.buildExecutionPlan(M, Request);

  auto Callbacks = makeFrontierCallbacks();
  Callbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (size < 32)
      return false;
    const uint8_t bytes[32] = {
        0x48, 0x89, 0x74, 0x24, 0x20, 0x66, 0x41, 0xF7, 0xD2, 0x90, 0x90,
        0x90, 0xE9, 0x4E, 0x6A, 0x05, 0x00, 0xBA, 0x9A, 0x14, 0xA0, 0xB9,
        0x49, 0x81, 0xE9, 0x04, 0x00, 0x00, 0x00, 0x44, 0x0F, 0xB6};
    std::memcpy(out, bytes, sizeof(bytes));
    return true;
  };
  Callbacks.can_decode_target = [](uint64_t) { return true; };

  (void)Orchestrator.discoverFrontierWork(
      M, Callbacks, omill::FrontierDiscoveryPhase::kOutputRootClosure);

  auto ProjectionLifter = makeProjectionLifter(M);
  auto Summary = Orchestrator.advanceFrontierWork(M, ProjectionLifter, Callbacks);

  EXPECT_EQ(Summary.failed_lift, 0u);
  EXPECT_EQ(Summary.failed_decode, 0u);
  EXPECT_GE(Summary.skipped_materialized, 1u);
  auto FrontierItems =
      omill::collectSessionFrontierWorkItems(Orchestrator.session());
  auto It = std::find_if(
      FrontierItems.begin(), FrontierItems.end(),
      [](const omill::FrontierWorkItem &item) {
        return item.target_pc && *item.target_pc == 0x401280u &&
               item.status == omill::FrontierWorkStatus::kSkippedMaterialized;
      });
  ASSERT_NE(It, FrontierItems.end());
  EXPECT_EQ(It->status, omill::FrontierWorkStatus::kSkippedMaterialized);
}

TEST_F(DevirtualizationOrchestratorTest,
       InvariantsCatchUnresolvedDispatchAndLiveRemillReads) {
  llvm::Module M("violations", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  auto *Dispatch = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "__omill_dispatch_call",
      M);
  auto *ReadTy = llvm::FunctionType::get(
      llvm::Type::getInt8Ty(Ctx),
      {llvm::PointerType::getUnqual(Ctx), llvm::Type::getInt64Ty(Ctx)},
      false);
  auto *Read = llvm::Function::Create(ReadTy, llvm::Function::ExternalLinkage,
                                      "__remill_read_memory_8", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Read, {Root->getArg(0), B.getInt64(0x10)});
  B.CreateCall(Dispatch, {Root->getArg(0), B.getInt64(0x401020), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Violations = Orchestrator.collectInvariantViolations(
      M, omill::DevirtualizationOutputMode::kNoABI);

  std::sort(Violations.begin(), Violations.end());
  std::vector<std::string> Expected = {
      "legacy_omill_dispatch_intrinsics",
      "live_remill_memory_intrinsics", "unresolved_dispatch_intrinsics"};
  EXPECT_EQ(Violations, Expected);
}

TEST_F(DevirtualizationOrchestratorTest,
       InvariantsCatchClosedSliceWrapperLaddersInAbiMode) {
  llvm::Module M("abi_wrappers", Ctx);
  M.addModuleFlag(llvm::Module::Override, "omill.closed_root_slice_scope", 1u);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Helper = addLiftedFunction(M, "blk_401020");
  Helper->addFnAttr("omill.abi_wrapper");

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Helper, {Root->getArg(0), Root->getArg(1), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  auto Violations = Orchestrator.collectInvariantViolations(
      M, omill::DevirtualizationOutputMode::kABI);

  EXPECT_EQ(Violations.size(), 1u);
  EXPECT_NE(std::find(Violations.begin(), Violations.end(),
                      "closed_slice_wrapper_ladder"),
            Violations.end());
}

}  // namespace



