#include "omill/Devirtualization/Orchestrator.h"

#include <gtest/gtest.h>

#include <algorithm>
#include <cstdlib>
#include <map>
#include <set>

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
  EXPECT_TRUE(std::any_of(
      Orchestrator.session().discovered_frontier_identities.begin(),
      Orchestrator.session().discovered_frontier_identities.end(),
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
  EXPECT_TRUE(std::find(Session.discovered_frontier_pcs.begin(),
                        Session.discovered_frontier_pcs.end(),
                        0x401020u) != Session.discovered_frontier_pcs.end());
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
  EXPECT_TRUE(std::any_of(
      Session.discovered_frontier_identities.begin(),
      Session.discovered_frontier_identities.end(),
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

  ASSERT_EQ(Session.discovered_frontier_identities.size(), 2u);
  EXPECT_EQ(Session.late_frontier_identities.size(), 2u);
  ASSERT_EQ(Session.discovered_frontier_work_items.size(), 2u);
  EXPECT_EQ(Session.late_frontier_work_items.size(), 2u);

  std::set<std::string> DistinctIdentities(
      Session.discovered_frontier_identities.begin(),
      Session.discovered_frontier_identities.end());
  EXPECT_EQ(DistinctIdentities.size(), 2u);
  std::set<std::string> DistinctWorkItemIdentities;
  for (const auto &item : Session.discovered_frontier_work_items)
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

  ASSERT_EQ(Session.discovered_frontier_work_items.size(), 2u);
  EXPECT_TRUE(std::all_of(
      Session.discovered_frontier_work_items.begin(),
      Session.discovered_frontier_work_items.end(),
      [](const omill::FrontierWorkItem &item) {
        return item.target_pc && *item.target_pc == 0x401020u &&
               item.exit_disposition ==
                   omill::VirtualExitDisposition::kVmExitNativeCallReenter;
      }));

  std::set<std::optional<uint64_t>> ContinuationVips;
  std::set<std::string> Identities;
  for (const auto &item : Session.discovered_frontier_work_items) {
    ContinuationVips.insert(item.continuation_vip_pc);
    Identities.insert(item.identity);
  }
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

  ASSERT_EQ(Session.late_frontier.size(), 2u);
  EXPECT_EQ(Session.late_frontier[0], 0x401000u);
  EXPECT_EQ(Session.late_frontier[1], 0x401000u);
  ASSERT_EQ(Session.late_frontier_work_items.size(), 2u);

  std::set<std::optional<uint64_t>> ContinuationVips;
  for (const auto &item : Session.late_frontier_work_items)
    ContinuationVips.insert(item.continuation_vip_pc);
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
  auto It = std::find_if(Session.discovered_frontier_work_items.begin(),
                         Session.discovered_frontier_work_items.end(),
                         [](const omill::FrontierWorkItem &item) {
                           return item.target_pc.has_value() &&
                                  *item.target_pc == 0x401120u &&
                                  item.identity.find("closure:") == 0;
                         });
  ASSERT_NE(It, Session.discovered_frontier_work_items.end());
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
  for (const auto &item : Orchestrator.session().discovered_frontier_work_items) {
    if (item.target_pc && *item.target_pc == 0x401120u &&
        item.identity.find("closure:") == 0) {
      ++matching;
      continuation_vips.insert(item.continuation_vip_pc);
    }
  }
  EXPECT_GE(matching, 2u);
  EXPECT_EQ(continuation_vips.size(), 2u);
  EXPECT_TRUE(continuation_vips.count(0x5000u) == 1u);
  EXPECT_TRUE(continuation_vips.count(0x6000u) == 1u);
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session,
      CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_native_exit, 1u);
  auto It = std::find_if(Orchestrator.session().frontier_work_by_identity.begin(),
                         Orchestrator.session().frontier_work_by_identity.end(),
                         [](const auto &entry) {
                           const auto &item = entry.second;
                           return item.target_pc && *item.target_pc == 0x401140u;
                         });
  ASSERT_NE(It, Orchestrator.session().frontier_work_by_identity.end());
  EXPECT_EQ(It->second.kind, omill::FrontierWorkKind::kNativeCallBoundary);
  EXPECT_TRUE(It->second.status == omill::FrontierWorkStatus::kClassifiedNativeExit ||
              It->second.status == omill::FrontierWorkStatus::kSkippedMaterialized);
  EXPECT_EQ(It->second.exit_disposition,
            omill::VirtualExitDisposition::kVmExitNativeCallReenter);
  auto *BoundaryDecl = M.getFunction("sub_401140");
  ASSERT_NE(BoundaryDecl, nullptr);
  EXPECT_TRUE(BoundaryDecl->isDeclaration());
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session,
      CallBoundaryCallbacks);

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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session,
      CallBoundaryCallbacks);

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

  auto Round = Orchestrator.runFrontierRound(
      M, *reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1)),
      *Orchestrator.session().iterative_session, VmEnterCallbacks,
      omill::FrontierDiscoveryPhase::kOutputRootClosure);
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

  auto Summary = Orchestrator.runFrontierIterations(
      M, *reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1)),
      *Orchestrator.session().iterative_session, VmEnterCallbacks,
      omill::FrontierDiscoveryPhase::kOutputRootClosure, 3,
      IterationCallbacks, &ImportCallbacks);

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

  auto CompatIt = Session.frontier_work_by_identity.find(EdgeId);
  ASSERT_NE(CompatIt, Session.frontier_work_by_identity.end());
  EXPECT_TRUE(CompatIt->second.target_pc.has_value());
  EXPECT_EQ(*CompatIt->second.target_pc, 0x401120u);
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

  auto Round = Orchestrator.runFrontierRound(
      M, *reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1)),
      *Orchestrator.session().iterative_session, VmEnterCallbacks,
      omill::FrontierDiscoveryPhase::kOutputRootClosure);
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session,
      CallBoundaryCallbacks);

  EXPECT_EQ(Summary.classified_native_exit, 0u);
  auto It = std::find_if(Orchestrator.session().frontier_work_by_identity.begin(),
                         Orchestrator.session().frontier_work_by_identity.end(),
                         [](const auto &entry) {
                           const auto &item = entry.second;
                           return item.target_pc && *item.target_pc == 0x4011C0u;
                         });
  ASSERT_NE(It, Orchestrator.session().frontier_work_by_identity.end());
  EXPECT_EQ(It->second.kind, omill::FrontierWorkKind::kLiftableBlock);
  EXPECT_EQ(It->second.status, omill::FrontierWorkStatus::kSkippedMaterialized);
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session, Callbacks);

  EXPECT_GE(Summary.failed_lift, 1u);
  auto It = std::find_if(Orchestrator.session().frontier_work_by_identity.begin(),
                         Orchestrator.session().frontier_work_by_identity.end(),
                         [](const auto &entry) {
                           const auto &item = entry.second;
                           return item.target_pc && *item.target_pc == 0x401220u &&
                                  item.identity.find("closure:") == 0;
                         });
  ASSERT_NE(It, Orchestrator.session().frontier_work_by_identity.end());
  EXPECT_EQ(It->second.kind, omill::FrontierWorkKind::kLiftableBlock);
  EXPECT_EQ(It->second.status, omill::FrontierWorkStatus::kFailedLift);
  EXPECT_EQ(It->second.failure_reason,
            "recovery_mode_deferred_liftable_block");
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session,
      VmEnterCallbacks);

  EXPECT_GE(Summary.classified_vm_enter, 1u);
  auto It = std::find_if(Orchestrator.session().frontier_work_by_identity.begin(),
                         Orchestrator.session().frontier_work_by_identity.end(),
                         [](const auto &entry) {
                           const auto &item = entry.second;
                           return item.target_pc && *item.target_pc == 0x4011c0u;
                         });
  ASSERT_NE(It, Orchestrator.session().frontier_work_by_identity.end());
  EXPECT_EQ(It->second.kind, omill::FrontierWorkKind::kVmEnterBoundary);
  EXPECT_EQ(It->second.status,
            omill::FrontierWorkStatus::kClassifiedVmEnter);
  auto *VmEnterDecl = M.getFunction("omill_vm_enter_target_4011C0");
  ASSERT_NE(VmEnterDecl, nullptr);
  EXPECT_EQ(VmEnterDecl->getFnAttribute("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_enter");
  EXPECT_TRUE(VmEnterDecl->hasFnAttribute("omill.vm_enter_target_pc"));
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session,
      CallBoundaryCallbacks);

  EXPECT_GE(Summary.classified_terminal, 1u);
  auto It = std::find_if(Orchestrator.session().frontier_work_by_identity.begin(),
                         Orchestrator.session().frontier_work_by_identity.end(),
                         [](const auto &entry) {
                           const auto &item = entry.second;
                           return item.target_pc && *item.target_pc == 0x401260u;
                         });
  ASSERT_NE(It, Orchestrator.session().frontier_work_by_identity.end());
  EXPECT_EQ(It->second.kind, omill::FrontierWorkKind::kTerminalBoundary);
  EXPECT_EQ(It->second.status,
            omill::FrontierWorkStatus::kClassifiedTerminal);
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

  auto *FakeLifter =
      reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
  auto Summary = Orchestrator.advanceFrontierWork(
      M, *FakeLifter, *Orchestrator.session().iterative_session, Callbacks);

  EXPECT_EQ(Summary.failed_lift, 0u);
  EXPECT_EQ(Summary.failed_decode, 0u);
  EXPECT_GE(Summary.skipped_materialized, 1u);
  auto It = std::find_if(
      Orchestrator.session().frontier_work_by_identity.begin(),
      Orchestrator.session().frontier_work_by_identity.end(),
      [](const auto &entry) {
        const auto &item = entry.second;
        return item.target_pc && *item.target_pc == 0x401280u &&
               item.status == omill::FrontierWorkStatus::kSkippedMaterialized;
      });
  ASSERT_NE(It, Orchestrator.session().frontier_work_by_identity.end());
  EXPECT_EQ(It->second.status,
            omill::FrontierWorkStatus::kSkippedMaterialized);
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
