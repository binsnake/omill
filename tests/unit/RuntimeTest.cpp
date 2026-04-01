#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/Runtime.h"

#include <gtest/gtest.h>

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include <string>
#include <algorithm>
#include <vector>

namespace {

class RuntimeTest : public ::testing::Test {
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

  static std::string childModuleIr(llvm::StringRef name,
                                   llvm::StringRef body = "ret ptr %2") {
    return "define ptr @" + name.str() +
           "(ptr %0, i64 %1, ptr %2) {\nentry:\n  " + body.str() + "\n}\n";
  }
};

TEST_F(RuntimeTest,
       RunOutputRecoveryImportsNoAbiExecutableChildrenThroughRuntime) {
  llvm::Module M("runtime_noabi_recovery", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  unsigned cleanup_calls = 0;
  unsigned patch_calls = 0;
  std::vector<uint64_t> patched_targets;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [](uint64_t target_pc, bool, bool, bool,
         bool) -> std::optional<omill::ChildLiftArtifact> {
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "define ptr @sub_401230(ptr %0, i64 %1, ptr %2) {\nentry:\n  ret "
            "ptr %2\n}\n";
        artifact.model_text =
            "root-slice root=0x401230 closed=true handler=sub_401230";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        plan.eligibility = omill::ImportEligibility::kImportable;
        plan.rejection_reason = omill::RecoveryRejectionReason::kNone;
        plan.imported_root = reinterpret_cast<llvm::Function *>(0x1);
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](const std::vector<uint64_t> &targets, llvm::StringRef,
          llvm::StringRef) -> unsigned {
        ++patch_calls;
        patched_targets = targets;
        return static_cast<unsigned>(targets.size());
      };
  callbacks.run_final_output_cleanup = [&]() { ++cleanup_calls; };

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_TRUE(summary.changed);
  EXPECT_EQ(summary.noabi_imported_children, 1u);
  EXPECT_EQ(summary.patched_declared_targets, 1u);
  EXPECT_EQ(cleanup_calls, 1u);
  EXPECT_EQ(patch_calls, 1u);
  ASSERT_EQ(patched_targets.size(), 1u);
  EXPECT_EQ(patched_targets.front(), 0x401230u);
  ASSERT_FALSE(summary.artifact_bundles.empty());
  auto bundle_it = std::find_if(
      summary.artifact_bundles.begin(), summary.artifact_bundles.end(),
      [](const omill::RoundArtifactBundle &bundle) {
        return bundle.stage ==
               omill::RuntimeArtifactStage::kOutputRecoveryImportRound;
      });
  ASSERT_NE(bundle_it, summary.artifact_bundles.end());
  EXPECT_EQ(bundle_it->label, "noabi_executable_children");
  EXPECT_NE(std::find(bundle_it->imported_targets.begin(),
                      bundle_it->imported_targets.end(), 0x401230u),
            bundle_it->imported_targets.end());
  auto imported_decision_it = std::find_if(
      bundle_it->import_decisions.begin(), bundle_it->import_decisions.end(),
      [](const omill::ImportDecisionArtifact &artifact) {
        return artifact.target_pc == 0x401230u && artifact.imported;
      });
  ASSERT_NE(imported_decision_it, bundle_it->import_decisions.end());
  EXPECT_EQ(imported_decision_it->eligibility,
            omill::ImportEligibility::kImportable);
  ASSERT_TRUE(imported_decision_it->selected_root_pc.has_value());
  EXPECT_EQ(*imported_decision_it->selected_root_pc, 0x401230u);
  EXPECT_NE(std::find(bundle_it->output_root_names.begin(),
                      bundle_it->output_root_names.end(),
                      std::string("sub_401000")),
            bundle_it->output_root_names.end());
}

TEST_F(RuntimeTest,
       RunOutputRecoveryImportsTrustedTerminalChildFromContinuationProof) {
  llvm::Module M("runtime_proof_terminal_child", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  auto &edge =
      orchestrator.session().graph.edge_facts_by_identity["closure:proof-edge"];
  edge.identity = "closure:proof-edge";
  edge.owner_function = "sub_401000";
  edge.site_index = 0;
  edge.site_pc = 0x401000u;
  edge.target_pc = 0x401230u;
  edge.executable_target = fact;
  edge.continuation_proof = omill::ContinuationProof{};
  edge.continuation_proof->edge_identity = edge.identity;
  edge.continuation_proof->raw_target_pc = 0x401230u;
  edge.continuation_proof->source_handler_name = "sub_401000";
  edge.continuation_proof->confidence =
      omill::ContinuationConfidence::kTrusted;
  edge.continuation_proof->liveness = omill::ContinuationLiveness::kLive;
  edge.continuation_proof->scheduling_class =
      omill::FrontierSchedulingClass::kTrustedLive;
  edge.continuation_proof->resolution_kind =
      omill::ContinuationResolutionKind::kExactFallthrough;
  edge.continuation_proof->import_disposition =
      omill::ContinuationImportDisposition::kImportable;
  edge.continuation_proof->selected_root_import_class =
      omill::ChildImportClass::kTrustedTerminalEntry;
  edge.continuation_proof->is_exact_fallthrough = true;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
  frontier_callbacks.is_executable_target = [](uint64_t) { return true; };
  frontier_callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  unsigned lift_calls = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        ++lift_calls;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = childModuleIr("sub_401230");
        artifact.model_text =
            "root-slice root=0x401230 closed=true handler=sub_401230";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        plan.eligibility = omill::ImportEligibility::kImportable;
        plan.rejection_reason = omill::RecoveryRejectionReason::kNone;
        plan.imported_root = reinterpret_cast<llvm::Function *>(0x1);
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](const std::vector<uint64_t> &, llvm::StringRef,
          llvm::StringRef) -> unsigned { return 1; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_TRUE(summary.changed);
  EXPECT_EQ(summary.noabi_imported_children, 1u);
  EXPECT_EQ(lift_calls, 1u);
}

TEST_F(RuntimeTest,
       RunOutputRecoveryImportsTrustedSelfLoopChildFromResolverEvidence) {
  llvm::Module M("runtime_resolver_promotes_exact_fallthrough", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kExactFallthrough;
  fact.exact_fallthrough_target = true;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  auto &edge = orchestrator
                   .session()
                   .graph.edge_facts_by_identity["closure:resolver-edge"];
  edge.identity = "closure:resolver-edge";
  edge.owner_function = "sub_401000";
  edge.site_index = 0;
  edge.site_pc = 0x401000u;
  edge.target_pc = 0x401230u;
  edge.executable_target = fact;
  edge.continuation_proof = omill::ContinuationProof{};
  edge.continuation_proof->edge_identity = edge.identity;
  edge.continuation_proof->raw_target_pc = 0x401230u;
  edge.continuation_proof->source_handler_name = "sub_401000";
  edge.continuation_proof->confidence =
      omill::ContinuationConfidence::kTrusted;
  edge.continuation_proof->liveness = omill::ContinuationLiveness::kLive;
  edge.continuation_proof->scheduling_class =
      omill::FrontierSchedulingClass::kTrustedLive;
  edge.continuation_proof->resolution_kind =
      omill::ContinuationResolutionKind::kExactFallthrough;
  edge.continuation_proof->import_disposition =
      omill::ContinuationImportDisposition::kRetryable;
  edge.continuation_proof->is_exact_fallthrough = true;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
  frontier_callbacks.is_executable_target = [](uint64_t) { return true; };
  frontier_callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  unsigned lift_calls = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        ++lift_calls;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "define ptr @sub_401230(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  br label %tail\n"
            "tail:\n"
            "  br label %tail\n"
            "}\n";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        plan.eligibility = omill::ImportEligibility::kImportable;
        plan.rejection_reason = omill::RecoveryRejectionReason::kNone;
        plan.imported_root = reinterpret_cast<llvm::Function *>(0x1);
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 1; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_TRUE(summary.changed);
  EXPECT_EQ(summary.noabi_imported_children, 1u);
  EXPECT_EQ(lift_calls, 1u);
  auto bundle_it = std::find_if(
      summary.artifact_bundles.begin(), summary.artifact_bundles.end(),
      [](const omill::RoundArtifactBundle &bundle) {
        return bundle.stage ==
               omill::RuntimeArtifactStage::kOutputRecoveryImportRound;
      });
  ASSERT_NE(bundle_it, summary.artifact_bundles.end());
  EXPECT_NE(std::find(bundle_it->recovery_quality.terminal_modeled_children.begin(),
                      bundle_it->recovery_quality.terminal_modeled_children.end(),
                      0x401230u),
            bundle_it->recovery_quality.terminal_modeled_children.end());
  EXPECT_FALSE(bundle_it->recovery_quality.functionally_recovered);
}

TEST_F(RuntimeTest,
       RunOutputRecoveryTreatsEngagedButEmptyProofAsMissingForResolver) {
  llvm::Module M("runtime_empty_proof_skips_reconstruction", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  auto &edge =
      orchestrator.session().graph.edge_facts_by_identity["closure:empty-proof"];
  edge.identity = "closure:empty-proof";
  edge.owner_function = "sub_401000";
  edge.site_index = 0;
  edge.site_pc = 0x401000u;
  edge.target_pc = 0x401230u;
  edge.executable_target = fact;
  edge.continuation_proof = omill::ContinuationProof{};

  omill::DevirtualizationRuntime runtime(orchestrator);

  unsigned decode_summary_calls = 0;
  unsigned lift_calls = 0;

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
  frontier_callbacks.decode_target_summary = [&](uint64_t) {
    ++decode_summary_calls;
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = 0x401230u;
    summary.next_pc = 0x401231u;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        ++lift_calls;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = childModuleIr("sub_401230");
        artifact.model_text =
            "root-slice root=0x401230 closed=true handler=sub_401230";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t, const omill::ChildLiftArtifact &,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.eligibility = omill::ImportEligibility::kRejected;
        plan.rejection_reason = omill::RecoveryRejectionReason::kUnsupported;
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 0; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_FALSE(summary.changed);
  EXPECT_EQ(decode_summary_calls, 0u);
  EXPECT_EQ(lift_calls, 1u);
}

TEST_F(RuntimeTest,
       RunOutputRecoveryPromotesTerminalProofFromBinaryExactFallthroughEvidence) {
  llvm::Module M("runtime_binary_exact_fallthrough_promotes_terminal_proof",
                 Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  auto &edge =
      orchestrator.session().graph.edge_facts_by_identity["closure:terminal"];
  edge.identity = "closure:terminal";
  edge.owner_function = "sub_401000";
  edge.site_index = 0;
  edge.site_pc = 0x401000u;
  edge.target_pc = 0x401230u;
  edge.executable_target = fact;
  edge.continuation_proof = omill::ContinuationProof{};
  edge.continuation_proof->edge_identity = edge.identity;
  edge.continuation_proof->raw_target_pc = 0x401230u;
  edge.continuation_proof->source_handler_name = "sub_401000";
  edge.continuation_proof->resolution_kind =
      omill::ContinuationResolutionKind::kTerminalModeled;
  edge.continuation_proof->import_disposition =
      omill::ContinuationImportDisposition::kRetryable;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
  frontier_callbacks.is_executable_target = [](uint64_t) { return true; };
  frontier_callbacks.can_decode_target = [](uint64_t) { return false; };
  frontier_callbacks.is_exact_call_fallthrough_target = [](uint64_t pc) {
    return pc == 0x401230u;
  };
  frontier_callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  unsigned lift_calls = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        ++lift_calls;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = childModuleIr("sub_401230");
        artifact.model_text =
            "root-slice root=0x401230 closed=true handler=sub_401230";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        plan.eligibility = omill::ImportEligibility::kImportable;
        plan.rejection_reason = omill::RecoveryRejectionReason::kNone;
        plan.imported_root = reinterpret_cast<llvm::Function *>(0x1);
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 1; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_TRUE(summary.changed);
  EXPECT_EQ(summary.noabi_imported_children, 1u);
  EXPECT_EQ(lift_calls, 1u);
}

TEST_F(RuntimeTest, RunOutputRecoveryCachesChildArtifactsAcrossDecisionSites) {
  llvm::Module M("runtime_child_cache", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.enable_precise_logs = true;
  options.max_noabi_executable_child_import_rounds = 1;

  unsigned lift_calls = 0;
  std::vector<std::string> logs;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.precise_log = [&](const omill::RuntimePreciseLogEvent &event) {
    logs.push_back(event.stage + ":" + event.message);
  };
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        ++lift_calls;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = childModuleIr("sub_401230");
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.selected_root_pc = artifact.selected_root_pc;
        plan.eligibility = omill::ImportEligibility::kRejected;
        plan.rejection_reason = omill::RecoveryRejectionReason::kUnsupported;
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 0; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_FALSE(summary.changed);
  EXPECT_EQ(lift_calls, 1u);
  EXPECT_NE(std::find(logs.begin(), logs.end(),
                      "child-cache-miss:lifting child artifact"),
            logs.end());
  EXPECT_NE(std::find(logs.begin(), logs.end(),
                      "child-cache-hit:reusing cached child artifact"),
            logs.end());
}

TEST_F(RuntimeTest,
       RunOutputRecoveryRejectsClosureWideRemillFunctionCallLeakBeforeImport) {
  llvm::Module M("runtime_closure_leak_rejected", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  bool import_attempted = false;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [](uint64_t target_pc, bool, bool, bool,
         bool) -> std::optional<omill::ChildLiftArtifact> {
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "declare ptr @__remill_function_call(ptr, i64, ptr)\n"
            "define ptr @blk_401230(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %r = call ptr @helper_401240(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %r\n"
            "}\n"
            "define ptr @helper_401240(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %r = call ptr @__remill_function_call(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %r\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401230 closed=true handler=blk_401230\n"
            "slice-handler blk_401230\n"
            "slice-handler helper_401240\n";
        return artifact;
      };
  callbacks.import_executable_child =
      [&](uint64_t, const omill::ChildLiftArtifact &,
          const omill::ChildImportPlan &, llvm::StringRef) {
        import_attempted = true;
        omill::ChildImportPlan plan;
        plan.eligibility = omill::ImportEligibility::kRejected;
        plan.rejection_reason = omill::RecoveryRejectionReason::kImportFailed;
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 0; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_FALSE(summary.changed);
  EXPECT_FALSE(import_attempted);
  EXPECT_NE(std::find_if(summary.notes.begin(), summary.notes.end(),
                         [](const std::string &note) {
                           return note.find("runtime_leak") != std::string::npos;
                         }),
            summary.notes.end());
  auto bundle_it = std::find_if(
      summary.artifact_bundles.begin(), summary.artifact_bundles.end(),
      [](const omill::RoundArtifactBundle &bundle) {
        return bundle.stage ==
               omill::RuntimeArtifactStage::kOutputRecoveryImportRound;
      });
  ASSERT_NE(bundle_it, summary.artifact_bundles.end());
  auto rejected_it = std::find_if(
      bundle_it->rejected_imports.begin(), bundle_it->rejected_imports.end(),
      [](const omill::RejectedImportArtifact &artifact) {
        return artifact.target_pc == 0x401230u &&
               artifact.reason ==
                   omill::RecoveryRejectionReason::kRuntimeLeak;
      });
  ASSERT_NE(rejected_it, bundle_it->rejected_imports.end());
  EXPECT_EQ(rejected_it->detail, "remill_function_call");
  auto rejected_decision_it = std::find_if(
      bundle_it->import_decisions.begin(), bundle_it->import_decisions.end(),
      [](const omill::ImportDecisionArtifact &artifact) {
        return artifact.target_pc == 0x401230u &&
               artifact.rejection_reason ==
                   omill::RecoveryRejectionReason::kRuntimeLeak;
      });
  ASSERT_NE(rejected_decision_it, bundle_it->import_decisions.end());
  EXPECT_EQ(rejected_decision_it->detail, "remill_function_call");
}

TEST_F(RuntimeTest,
       RunOutputRecoveryPassesRuntimeApprovedDeclarationCalleesToImporter) {
  llvm::Module M("runtime_decl_allowlist", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FrontierCallbacks frontier_callbacks;
  frontier_callbacks.is_code_address = [](uint64_t) { return true; };
  frontier_callbacks.has_defined_target = [](uint64_t) { return false; };
  frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  bool saw_feclearexcept = false;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [](uint64_t target_pc, bool, bool, bool,
         bool) -> std::optional<omill::ChildLiftArtifact> {
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "declare i32 @feclearexcept(i32)\n"
            "define ptr @blk_401230(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %c = call i32 @feclearexcept(i32 0)\n"
            "  ret ptr %2\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401230 closed=true handler=blk_401230\n"
            "slice-handler blk_401230\n";
        return artifact;
      };
  callbacks.import_executable_child =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &plan, llvm::StringRef) {
        if (std::find(plan.allowed_declaration_callees.begin(),
                      plan.allowed_declaration_callees.end(),
                      std::string("feclearexcept")) !=
            plan.allowed_declaration_callees.end()) {
          saw_feclearexcept = true;
        }
        omill::ChildImportPlan accepted;
        accepted.target_pc = target_pc;
        accepted.selected_root_pc = artifact.selected_root_pc;
        accepted.eligibility = omill::ImportEligibility::kImportable;
        accepted.rejection_reason = omill::RecoveryRejectionReason::kNone;
        accepted.imported_root = reinterpret_cast<llvm::Function *>(0x1);
        accepted.allowed_declaration_callees = plan.allowed_declaration_callees;
        return accepted;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401230u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 1; };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_TRUE(summary.changed);
  EXPECT_TRUE(saw_feclearexcept);
  EXPECT_EQ(summary.noabi_imported_children, 1u);
}

TEST_F(RuntimeTest, RunOutputRecoveryEmitsPreciseLogsWhenEnabled) {
  llvm::Module M("runtime_precise_logs", Ctx);
  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = false;
  options.allow_abi_postmain_rounds = true;
  options.enable_precise_logs = true;

  std::vector<std::string> log_trace;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.precise_log = [&](const omill::RuntimePreciseLogEvent &event) {
    log_trace.push_back(event.component + ":" + event.stage + ":" +
                        event.message);
  };
  callbacks.run_final_output_cleanup = [] {};

  (void)runtime.runOutputRecovery(M, nullptr, nullptr, nullptr, options,
                                  callbacks);

  EXPECT_NE(std::find(log_trace.begin(), log_trace.end(),
                      "output-recovery:abi-step-begin:"
                      "initial_final_output_cleanup"),
            log_trace.end());
  EXPECT_NE(std::find(log_trace.begin(), log_trace.end(),
                      "output-recovery:abi-step-end:"
                      "initial_final_output_cleanup"),
            log_trace.end());
}

TEST_F(RuntimeTest, RunOutputRecoveryOwnsAbiCleanupSequencing) {
  llvm::Module M("runtime_abi_recovery", Ctx);
  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::OutputRecoveryOptions options;
  options.raw_binary = false;
  options.no_abi = false;
  options.allow_abi_postmain_rounds = true;

  std::vector<std::string> trace;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.note_abi_post_cleanup_step = [&](llvm::StringRef label,
                                             bool starting) {
    trace.push_back((starting ? "begin:" : "end:") + label.str());
  };
  callbacks.sanitize_remaining_poison_native_helper_args = [&]() {
    trace.push_back("sanitize");
  };
  callbacks.erase_noop_self_recursive_native_calls = [&]() {
    trace.push_back("erase");
  };
  callbacks.run_final_output_cleanup = [&]() { trace.push_back("cleanup"); };
  callbacks.prune_to_defined_output_root_closure = [&]() {
    trace.push_back("prune");
  };
  callbacks.rerun_late_output_root_target_pipeline = [&]() {
    trace.push_back("rerun");
  };

  auto summary =
      runtime.runOutputRecovery(M, nullptr, nullptr, nullptr, options, callbacks);

  EXPECT_FALSE(summary.changed);
  EXPECT_EQ(trace,
            (std::vector<std::string>{
                "begin:sanitize_remaining_poison_native_helper_args",
                "sanitize",
                "end:sanitize_remaining_poison_native_helper_args",
                "begin:erase_noop_self_recursive_native_calls",
                "erase",
                "end:erase_noop_self_recursive_native_calls",
                "begin:initial_final_output_cleanup",
                "cleanup",
                "end:initial_final_output_cleanup",
                "begin:initial_prune_defined_output_root_closure",
                "prune",
                "end:initial_prune_defined_output_root_closure",
                "begin:post_prune_final_output_cleanup",
                "cleanup",
                "end:post_prune_final_output_cleanup",
                "begin:initial_rerun_late_output_root_target_pipeline",
                "rerun",
                "end:initial_rerun_late_output_root_target_pipeline",
            }));
  ASSERT_FALSE(summary.artifact_bundles.empty());
  const auto &bundle = summary.artifact_bundles.back();
  auto has_cleanup_label = [&](const char *label) {
    return std::find_if(
               bundle.cleanup_actions.begin(), bundle.cleanup_actions.end(),
               [&](const omill::CleanupActionArtifact &artifact) {
                 return artifact.label == label;
               }) != bundle.cleanup_actions.end();
  };
  EXPECT_TRUE(has_cleanup_label("initial_final_output_cleanup"));
  EXPECT_TRUE(has_cleanup_label("initial_prune_defined_output_root_closure"));
  EXPECT_TRUE(has_cleanup_label("initial_rerun_late_output_root_target_pipeline"));
}

TEST_F(RuntimeTest, FinalizeOutputReturnsProtectorReportOnlyWhenEnabled) {
  llvm::Module M("runtime_finalize", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  auto disabled = runtime.finalizeOutput(M, false);
  EXPECT_FALSE(disabled.has_protector_report);

  auto enabled = runtime.finalizeOutput(M, true);
  EXPECT_TRUE(enabled.has_protector_report);
}

TEST_F(RuntimeTest, FinalizeOutputRecordsArtifactBundleForReachablePlaceholder) {
  llvm::Module M("runtime_finalize_bundle", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401230u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401230), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  auto enabled = runtime.finalizeOutput(M, true);
  ASSERT_TRUE(enabled.has_protector_report);
  ASSERT_EQ(enabled.artifact_bundles.size(), 1u);
  const auto &bundle = enabled.artifact_bundles.front();
  EXPECT_EQ(bundle.stage, omill::RuntimeArtifactStage::kFinalization);
  EXPECT_NE(std::find(bundle.executable_placeholder_targets.begin(),
                      bundle.executable_placeholder_targets.end(), 0x401230u),
            bundle.executable_placeholder_targets.end());
  auto cleanup_it = std::find_if(
      bundle.cleanup_actions.begin(), bundle.cleanup_actions.end(),
      [](const omill::CleanupActionArtifact &artifact) {
        return artifact.label == "build_validation_report";
      });
  EXPECT_NE(cleanup_it, bundle.cleanup_actions.end());
  EXPECT_NE(std::find(bundle.output_root_names.begin(),
                      bundle.output_root_names.end(),
                      std::string("sub_401000")),
            bundle.output_root_names.end());
}

TEST_F(RuntimeTest,
       FinalStateRecoveryPlannerKeepsTerminalModeledExecutableChild) {
  llvm::Module M("runtime_final_state_terminal_retry", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401234", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401234u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kTerminal;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401234), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::OutputRecoveryOptions options;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = childModuleIr("sub_401234");
        artifact.model_text =
            "root-slice root=0x401234 closed=true handler=sub_401234";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.eligibility = omill::ImportEligibility::kRejected;
        plan.rejection_reason = omill::RecoveryRejectionReason::kNotSelfContained;
        plan.rejection_detail = "terminal_only_child";
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401234u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 0; };
  callbacks.run_final_output_cleanup = [] {};

  (void)runtime.runOutputRecovery(M, nullptr, nullptr, nullptr, options,
                                  callbacks);
  (void)runtime.finalizeOutput(M, true);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  auto plan = runtime.planFinalStateRecovery(M, request);
  ASSERT_TRUE(plan.has_value());
  auto action_it = std::find_if(
      plan->actions.begin(), plan->actions.end(),
      [](const omill::FinalStateRecoveryAction &action) {
        return action.target_pc == 0x401234u;
      });
  ASSERT_NE(action_it, plan->actions.end());
  EXPECT_EQ(action_it->kind,
            omill::FinalStateRecoveryActionKind::kKeepModeledPlaceholder);
  EXPECT_EQ(action_it->reason, "terminal_modeled_child");

  auto bundle = runtime.runFinalStateRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  ASSERT_FALSE(bundle->planned_recovery_actions.empty());
  ASSERT_FALSE(bundle->executed_recovery_actions.empty());
  auto executed_it = std::find_if(
      bundle->executed_recovery_actions.begin(),
      bundle->executed_recovery_actions.end(),
      [](const omill::ExecutedRecoveryActionArtifact &action) {
        return action.target_pc == 0x401234u;
      });
  ASSERT_NE(executed_it, bundle->executed_recovery_actions.end());
  EXPECT_FALSE(executed_it->attempted);
  EXPECT_EQ(executed_it->disposition,
            omill::FinalStateRecoveryDisposition::kKeptPlaceholder);
  EXPECT_EQ(executed_it->detail, "terminal_modeled_child");
}

TEST_F(RuntimeTest, FinalStateRecoveryPlannerHardRejectsRuntimeLeakChild) {
  llvm::Module M("runtime_final_state_runtime_leak", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401235", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401235u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401235), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::OutputRecoveryOptions options;
  options.no_abi = true;
  options.use_block_lifting = true;
  options.allow_noabi_postmain_rounds = true;
  options.max_noabi_executable_child_import_rounds = 1;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "declare ptr @__remill_function_call(ptr, i64, ptr)\n"
            "define ptr @sub_401235(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %call = call ptr @__remill_function_call(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %call\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401235 closed=true handler=sub_401235";
        return artifact;
      };
  callbacks.import_executable_child =
      [](uint64_t target_pc, const omill::ChildLiftArtifact &,
         const omill::ChildImportPlan &, llvm::StringRef) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.eligibility = omill::ImportEligibility::kRejected;
        plan.rejection_reason = omill::RecoveryRejectionReason::kRuntimeLeak;
        plan.rejection_detail = "remill_function_call";
        return plan;
      };
  callbacks.collect_executable_placeholder_declaration_targets = [] {
    return std::vector<uint64_t>{0x401235u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [](const std::vector<uint64_t> &, llvm::StringRef,
         llvm::StringRef) -> unsigned { return 0; };
  callbacks.run_final_output_cleanup = [] {};

  (void)runtime.runOutputRecovery(M, nullptr, nullptr, nullptr, options,
                                  callbacks);
  (void)runtime.finalizeOutput(M, true);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  auto plan = runtime.planFinalStateRecovery(M, request);
  ASSERT_TRUE(plan.has_value());
  auto action_it = std::find_if(
      plan->actions.begin(), plan->actions.end(),
      [](const omill::FinalStateRecoveryAction &action) {
        return action.target_pc == 0x401235u;
      });
  ASSERT_NE(action_it, plan->actions.end());
  EXPECT_EQ(action_it->kind, omill::FinalStateRecoveryActionKind::kHardReject);
}

TEST_F(RuntimeTest, FinalStateRecoveryPlannerModelsBoundaryReentryTarget) {
  llvm::Module M("runtime_final_state_boundary_retry", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401400", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Boundary,
               {Root->getArg(0), B.getInt64(0x401400), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401400u;
  boundary_fact.native_target_pc = 0x401400u;
  boundary_fact.continuation_pc = 0x401410u;
  boundary_fact.reenters_vm = true;
  orchestrator.session().graph.boundary_facts_by_target[0x401400u].target_pc =
      0x401400u;
  orchestrator.session().graph.boundary_facts_by_target[0x401400u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);
  (void)runtime.finalizeOutput(M, true);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  auto plan = runtime.planFinalStateRecovery(M, request);
  ASSERT_TRUE(plan.has_value());
  auto action_it = std::find_if(
      plan->actions.begin(), plan->actions.end(),
      [](const omill::FinalStateRecoveryAction &action) {
        return action.target_pc == 0x401400u;
      });
  ASSERT_NE(action_it, plan->actions.end());
  EXPECT_EQ(action_it->kind,
            omill::FinalStateRecoveryActionKind::kKeepModeledPlaceholder);
  EXPECT_EQ(action_it->reason, "modeled_reentry_boundary");

  omill::OutputRecoveryCallbacks callbacks;
  auto bundle = runtime.runFinalStateRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  EXPECT_NE(std::find(bundle->recovery_quality.modeled_reentry_boundaries.begin(),
                      bundle->recovery_quality.modeled_reentry_boundaries.end(),
                      0x401400u),
            bundle->recovery_quality.modeled_reentry_boundaries.end());
}

TEST_F(RuntimeTest, FinalStateRecoveryPlannerSkipsQuarantinedSelectorArm) {
  llvm::Module M("runtime_final_state_quarantined_skip", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401236", M);
  omill::ExecutableTargetFact fact;
  fact.raw_target_pc = 0x401236u;
  fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*Placeholder, fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder,
               {Root->getArg(0), B.getInt64(0x401236), Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  auto &edge =
      orchestrator.session().graph.edge_facts_by_identity["closure:quarantine"];
  edge.identity = "closure:quarantine";
  edge.owner_function = "sub_401000";
  edge.target_pc = 0x401236u;
  edge.executable_target = fact;
  edge.continuation_proof = omill::ContinuationProof{};
  edge.continuation_proof->raw_target_pc = 0x401236u;
  edge.continuation_proof->liveness =
      omill::ContinuationLiveness::kQuarantined;
  edge.continuation_proof->scheduling_class =
      omill::FrontierSchedulingClass::kQuarantinedSelectorArm;
  edge.continuation_proof->resolution_kind =
      omill::ContinuationResolutionKind::kQuarantinedSelectorArm;
  edge.continuation_proof->import_disposition =
      omill::ContinuationImportDisposition::kDeferred;

  omill::DevirtualizationRuntime runtime(orchestrator);
  (void)runtime.finalizeOutput(M, true);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  auto plan = runtime.planFinalStateRecovery(M, request);
  ASSERT_TRUE(plan.has_value());
  EXPECT_TRUE(plan->actions.empty());
}

}  // namespace
