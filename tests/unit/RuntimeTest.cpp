#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/Runtime.h"
#include "omill/Utils/LiftedNames.h"

#include <gtest/gtest.h>

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include <cstring>
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

  static llvm::Function *addVoidFunction(llvm::Module &M, llvm::StringRef name,
                                         llvm::GlobalValue::LinkageTypes linkage =
                                             llvm::Function::ExternalLinkage) {
    auto *Fn = llvm::Function::Create(
        llvm::FunctionType::get(llvm::Type::getVoidTy(M.getContext()), false),
        linkage, name, M);
    llvm::BasicBlock::Create(M.getContext(), "entry", Fn);
    return Fn;
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
       RunOutputRecoveryCachesFailedChildLiftsAcrossImportRounds) {
  llvm::Module M("runtime_child_lift_failure_cached", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *SuccessPlaceholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);
  omill::ExecutableTargetFact success_fact;
  success_fact.raw_target_pc = 0x401230u;
  success_fact.kind = omill::ExecutableTargetKind::kExecutablePlaceholder;
  success_fact.trust = omill::ExecutableTargetTrust::kUntrustedExecutable;
  omill::writeExecutableTargetFact(*SuccessPlaceholder, success_fact);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(SuccessPlaceholder,
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
  options.max_noabi_executable_child_import_rounds = 2;

  unsigned lift_calls = 0;
  unsigned patch_calls = 0;
  unsigned negative_cache_hits = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.precise_log = [&](const omill::RuntimePreciseLogEvent &event) {
    if (event.stage == "child-cache-negative-hit" &&
        event.target_pc == std::optional<uint64_t>(0x401231u)) {
      ++negative_cache_hits;
    }
  };
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        ++lift_calls;
        if (target_pc == 0x401231u)
          return std::nullopt;
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
    return std::vector<uint64_t>{0x401230u, 0x401231u};
  };
  callbacks.patch_declared_lifted_or_block_calls_to_defined_targets =
      [&](const std::vector<uint64_t> &, llvm::StringRef,
          llvm::StringRef) -> unsigned {
        ++patch_calls;
        return 1u;
      };
  callbacks.run_final_output_cleanup = [] {};

  auto summary = runtime.runOutputRecovery(M, nullptr, nullptr,
                                           &frontier_callbacks, options,
                                           callbacks);

  EXPECT_TRUE(summary.changed);
  EXPECT_EQ(summary.noabi_imported_children, 1u);
  EXPECT_EQ(patch_calls, 1u);
  EXPECT_EQ(lift_calls, 2u);
  EXPECT_EQ(negative_cache_hits, 0u);
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
       RunOutputRecoverySeparatesLoweringHelpersFromSemanticImports) {
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

  bool saw_feclearexcept_allowed = false;
  bool saw_feclearexcept_lowering_helper = false;
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
          saw_feclearexcept_allowed = true;
        }
        if (std::find(plan.lowering_helper_callees.begin(),
                      plan.lowering_helper_callees.end(),
                      std::string("feclearexcept")) !=
            plan.lowering_helper_callees.end()) {
          saw_feclearexcept_lowering_helper = true;
        }
        omill::ChildImportPlan accepted;
        accepted.target_pc = target_pc;
        accepted.selected_root_pc = artifact.selected_root_pc;
        accepted.eligibility = omill::ImportEligibility::kImportable;
        accepted.rejection_reason = omill::RecoveryRejectionReason::kNone;
        accepted.imported_root = reinterpret_cast<llvm::Function *>(0x1);
        accepted.allowed_declaration_callees = plan.allowed_declaration_callees;
        accepted.lowering_helper_callees = plan.lowering_helper_callees;
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
  EXPECT_FALSE(saw_feclearexcept_allowed);
  EXPECT_TRUE(saw_feclearexcept_lowering_helper);
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

TEST_F(RuntimeTest,
       FinalizeOutputExcludesLoweringHelpersFromAcceptedExternalLeafCalls) {
  llvm::Module M("runtime_lowering_helper_quality", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *HelperTy = llvm::FunctionType::get(llvm::Type::getInt32Ty(Ctx),
                                           {llvm::Type::getInt32Ty(Ctx)},
                                           false);
  auto *Helper = llvm::Function::Create(
      HelperTy, llvm::Function::ExternalLinkage, "feclearexcept", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Helper, {B.getInt32(0)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);
  auto summary = runtime.finalizeOutput(M, /*devirtualization_enabled=*/false);

  ASSERT_EQ(summary.artifact_bundles.size(), 1u);
  const auto &bundle = summary.artifact_bundles.front();
  EXPECT_NE(std::find(bundle.lowering_helper_callees.begin(),
                      bundle.lowering_helper_callees.end(),
                      std::string("feclearexcept")),
            bundle.lowering_helper_callees.end());
  EXPECT_NE(std::find(bundle.recovery_quality.lowering_helper_callees.begin(),
                      bundle.recovery_quality.lowering_helper_callees.end(),
                      std::string("feclearexcept")),
            bundle.recovery_quality.lowering_helper_callees.end());
  EXPECT_EQ(std::find(bundle.recovery_quality.accepted_external_leaf_calls.begin(),
                      bundle.recovery_quality.accepted_external_leaf_calls.end(),
                      std::string("feclearexcept")),
            bundle.recovery_quality.accepted_external_leaf_calls.end());
}

TEST_F(RuntimeTest, FinalizeOutputProtectorReportSkipsLoweringHelpers) {
  llvm::Module M("runtime_lowering_helper_protector_report", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *HelperTy = llvm::FunctionType::get(llvm::Type::getInt32Ty(Ctx),
                                           {llvm::Type::getInt32Ty(Ctx)},
                                           false);
  auto *Helper = llvm::Function::Create(
      HelperTy, llvm::Function::ExternalLinkage, "feclearexcept", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Helper, {B.getInt32(0)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);
  auto summary = runtime.finalizeOutput(M, /*devirtualization_enabled=*/true);

  ASSERT_TRUE(summary.has_protector_report);
  EXPECT_EQ(std::find_if(summary.protector_report.issues.begin(),
                         summary.protector_report.issues.end(),
                         [](const auto &issue) {
                           return issue.callee_name == "feclearexcept";
                         }),
            summary.protector_report.issues.end());
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
       ClassifyRecoveryQualityRejectsDispatcherShellAbiWrapper) {
  llvm::Module M("runtime_dispatcher_shell", Ctx);
  auto *Internal =
      addVoidFunction(M, "__omill_internal_output_root_sub_401000",
                      llvm::Function::InternalLinkage);
  Internal->addFnAttr("omill.output_root");
  Internal->addFnAttr("omill.internal_output_root", "1");
  Internal->getEntryBlock().eraseFromParent();
  auto *InternalEntry = llvm::BasicBlock::Create(Ctx, "entry", Internal);
  auto *Loop = llvm::BasicBlock::Create(Ctx, "tailrecurse", Internal);
  llvm::IRBuilder<> InternalEntryBuilder(InternalEntry);
  InternalEntryBuilder.CreateBr(Loop);
  llvm::IRBuilder<> LoopBuilder(Loop);
  LoopBuilder.CreateBr(Loop);

  auto *Wrapper = addVoidFunction(M, "sub_401000");
  Wrapper->addFnAttr("omill.output_root");
  auto &WrapperEntry = Wrapper->getEntryBlock();
  llvm::IRBuilder<> B(&WrapperEntry);
  auto *stack_ty = llvm::ArrayType::get(B.getInt8Ty(), 4096);
  auto *stack = B.CreateAlloca(stack_ty, nullptr, "state.stack");
  auto *stack_i8 =
      B.CreateBitCast(stack, llvm::PointerType::getUnqual(Ctx), "state.i8");
  B.CreateMemSet(stack_i8, B.getInt8(0), 4096, llvm::MaybeAlign(16));
  B.CreateCall(Internal);
  B.CreateUnreachable();

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  auto quality = runtime.classifyRecoveryQuality(M);
  EXPECT_TRUE(quality.dispatcher_shell);
  EXPECT_TRUE(quality.dispatcher_heavy);
  EXPECT_FALSE(quality.functionally_recovered);

  auto finalization = runtime.finalizeOutput(M, true);
  ASSERT_TRUE(finalization.recovery_quality.has_value());
  EXPECT_TRUE(finalization.recovery_quality->dispatcher_shell);
  EXPECT_FALSE(finalization.recovery_quality->functionally_recovered);
}

TEST_F(RuntimeTest,
       ClassifyRecoveryQualityDoesNotTreatVisibleBoundaryTailAsDispatcherShell) {
  llvm::Module M("runtime_visible_boundary_tail", Ctx);
  auto *Internal =
      addVoidFunction(M, "__omill_internal_output_root_sub_401001",
                      llvm::Function::InternalLinkage);
  Internal->addFnAttr("omill.output_root");
  Internal->addFnAttr("omill.internal_output_root", "1");
  auto *Boundary = llvm::Function::Create(
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false),
      llvm::Function::ExternalLinkage, "omill_native_target_401400", M);
  auto &InternalEntry = Internal->getEntryBlock();
  llvm::IRBuilder<> InternalBuilder(&InternalEntry);
  InternalBuilder.CreateCall(Boundary);
  InternalBuilder.CreateUnreachable();

  auto *Wrapper = addVoidFunction(M, "sub_401001");
  Wrapper->addFnAttr("omill.output_root");
  auto &WrapperEntry = Wrapper->getEntryBlock();
  llvm::IRBuilder<> B(&WrapperEntry);
  auto *stack_ty = llvm::ArrayType::get(B.getInt8Ty(), 4096);
  auto *stack = B.CreateAlloca(stack_ty, nullptr, "state.stack");
  auto *stack_i8 =
      B.CreateBitCast(stack, llvm::PointerType::getUnqual(Ctx), "state.i8");
  B.CreateMemSet(stack_i8, B.getInt8(0), 4096, llvm::MaybeAlign(16));
  B.CreateCall(Internal);
  B.CreateUnreachable();

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  auto quality = runtime.classifyRecoveryQuality(M);
  EXPECT_FALSE(quality.dispatcher_shell);
  EXPECT_FALSE(quality.functionally_recovered);
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

TEST_F(RuntimeTest,
       BoundaryTailRecoveryLiftsControlledReturnContinuationAndReportsIt) {
  llvm::Module M("runtime_boundary_controlled_return", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401420", M);
  auto *Continuation = addLiftedFunction(M, "blk_401499");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401420),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401420u;
  boundary_fact.native_target_pc = 0x401420u;
  boundary_fact.continuation_pc = 0x401430u;
  boundary_fact.controlled_return_pc = 0x401499u;
  boundary_fact.return_address_control_kind =
      omill::VirtualReturnAddressControlKind::kRedirectedConstant;
  boundary_fact.suppresses_normal_fallthrough = true;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401420u].target_pc =
      0x401420u;
  orchestrator.session().graph.boundary_facts_by_target[0x401420u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x401499u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                                  size_t size) {
          if (size < 8)
            return false;
          const uint8_t bytes[8] = {0x90, 0x90, 0x90, 0x90,
                                    0x90, 0x90, 0x90, 0x90};
          std::memcpy(out, bytes, sizeof(bytes));
          for (size_t i = sizeof(bytes); i < size; ++i)
            out[i] = 0x90;
          return true;
        };
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401420u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
  EXPECT_EQ(result_it->detail, "controlled_return_continuation_lifted");
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401499u));
  EXPECT_NE(
      std::find(bundle->recovery_quality.lifted_controlled_return_continuations
                    .begin(),
                bundle->recovery_quality.lifted_controlled_return_continuations
                    .end(),
                0x401499u),
      bundle->recovery_quality.lifted_controlled_return_continuations.end());
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryKeepsUnresolvedControlledReturnVisible) {
  llvm::Module M("runtime_boundary_controlled_return_unresolved", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401520", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401520),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401520u;
  boundary_fact.native_target_pc = 0x401520u;
  boundary_fact.continuation_pc = 0x401530u;
  boundary_fact.return_address_control_kind =
      omill::VirtualReturnAddressControlKind::kStackCellControlled;
  boundary_fact.suppresses_normal_fallthrough = true;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401520u].target_pc =
      0x401520u;
  orchestrator.session().graph.boundary_facts_by_target[0x401520u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401520u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->detail, "controlled_return_unresolved");
  EXPECT_NE(std::find(bundle->recovery_quality.controlled_return_unresolved.begin(),
                      bundle->recovery_quality.controlled_return_unresolved.end(),
                      0x401520u),
            bundle->recovery_quality.controlled_return_unresolved.end());
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryClassifiesJumpTailContinuationCellAsControlledReturn) {
  llvm::Module M("runtime_boundary_jump_tail_controlled_return", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401700", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401700),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [](uint64_t target_pc, bool no_abi, bool enable_gsd,
         bool enable_recovery_mode,
         bool dump_virtual_model) -> std::optional<omill::ChildLiftArtifact> {
        (void)no_abi;
        (void)enable_gsd;
        (void)enable_recovery_mode;
        (void)dump_virtual_model;
        if (target_pc != 0x401700u)
          return std::nullopt;

        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text = R"(
define ptr @sub_401700(ptr %state, i64 %pc, ptr %memory) {
entry:
  %slot = alloca i64, align 8
  store i64 4196097, ptr %slot, align 8
  call void @helper(ptr %slot, ptr %state)
  %target = load i64, ptr %slot, align 8
  %result = call ptr @__remill_jump(ptr %state, i64 %target, ptr %memory)
  ret ptr %result
}

define internal void @helper(ptr %slot, ptr %state) {
entry:
  %gep = getelementptr i8, ptr %state, i64 2248
  %value = load i64, ptr %gep, align 8
  store i64 %value, ptr %slot, align 8
  ret void
}

declare ptr @__remill_jump(ptr, i64, ptr)
)";
        return artifact;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401700u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->detail, "controlled_return_unresolved");
  EXPECT_NE(std::find(bundle->recovery_quality.controlled_return_unresolved.begin(),
                      bundle->recovery_quality.controlled_return_unresolved.end(),
                      0x401700u),
            bundle->recovery_quality.controlled_return_unresolved.end());
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryLiftsModeledReentryBoundaryContinuation) {
  llvm::Module M("runtime_boundary_continuation_recovery", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401400", M);
  auto *Continuation = addLiftedFunction(M, "blk_401410");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401400),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401400u;
  boundary_fact.native_target_pc = 0x401400u;
  boundary_fact.continuation_pc = 0x401410u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401400u].target_pc =
      0x401400u;
  orchestrator.session().graph.boundary_facts_by_target[0x401400u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  unsigned cleanup_calls = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.run_final_output_cleanup = [&]() { ++cleanup_calls; };
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x401410u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
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
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  EXPECT_TRUE(bundle->changed);
  EXPECT_GE(cleanup_calls, 1u);
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401400u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401410u));

  bool saw_materialized_boundary = false;
  bool saw_continuation = false;
  for (auto &F : M) {
    if (F.isDeclaration() || &F == Root || &F == Continuation)
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!CB || !CB->getCalledFunction())
          continue;
        if (CB->getCalledFunction()->getName() != Continuation->getName())
          continue;
        saw_materialized_boundary = true;
        saw_continuation = true;
        continue;
      }
    }
  }
  EXPECT_TRUE(saw_materialized_boundary);
  EXPECT_TRUE(saw_continuation);
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryFindsContinuationByNativeTargetBoundaryFact) {
  llvm::Module M("runtime_boundary_continuation_native_target_lookup", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401500", M);
  auto *Continuation = addLiftedFunction(M, "blk_401510");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401500),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x4015A0u;
  boundary_fact.native_target_pc = 0x401500u;
  boundary_fact.continuation_pc = 0x401510u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x4015A0u].target_pc =
      0x4015A0u;
  orchestrator.session().graph.boundary_facts_by_target[0x4015A0u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x401510u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                                  size_t size) {
          if (size < 8)
            return false;
          const uint8_t bytes[8] = {0xE8, 0x0B, 0x00, 0x00,
                                    0x00, 0x90, 0x90, 0x90};
          std::memcpy(out, bytes, sizeof(bytes));
          for (size_t i = sizeof(bytes); i < size; ++i)
            out[i] = 0x90;
          return true;
        };
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401500u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401510u));

  auto *BoundaryStub = M.getFunction("omill_native_target_401500");
  ASSERT_NE(BoundaryStub, nullptr);
  EXPECT_FALSE(BoundaryStub->isDeclaration());
  EXPECT_EQ(omill::extractStructuralCodeTargetPC(*BoundaryStub), 0x401500u);
  bool saw_continuation = false;
  for (auto &BB : *BoundaryStub) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      if (CB->getCalledFunction()->getName() == Continuation->getName())
        saw_continuation = true;
    }
  }
  EXPECT_TRUE(saw_continuation);
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryDoesNotCountVmEnterPlaceholderAsLiftedContinuation) {
  llvm::Module M("runtime_boundary_continuation_placeholder_only", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401520", M);
  auto *VmEnterPlaceholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_401530", M);
  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x401530u;
  vm_enter_fact.continuation_pc = 0x401530u;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterPlaceholder, vm_enter_fact);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401520),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401520u;
  boundary_fact.native_target_pc = 0x401520u;
  boundary_fact.continuation_pc = 0x401530u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401520u].target_pc =
      0x401520u;
  orchestrator.session().graph.boundary_facts_by_target[0x401520u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);
  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        if (!Boundary->isDeclaration())
          return false;
        auto *entry = llvm::BasicBlock::Create(Ctx, "entry", Boundary);
        llvm::IRBuilder<> B(entry);
        auto *call = B.CreateCall(
            VmEnterPlaceholder,
            {Boundary->getArg(0), B.getInt64(0x401530), Boundary->getArg(2)});
        B.CreateRet(call);
        return true;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401520u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kKeptModeledBoundary);
  EXPECT_EQ(result_it->detail, "boundary_reentry_still_modeled");
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryUsesModuleBoundaryContinuationWhenSessionIsPartial) {
  llvm::Module M("runtime_boundary_continuation_module_fallback", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401600", M);
  auto *Continuation = addLiftedFunction(M, "blk_401610");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401600),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact session_boundary_fact;
  session_boundary_fact.boundary_pc = 0x4016A0u;
  session_boundary_fact.native_target_pc = 0x401600u;
  session_boundary_fact.reenters_vm = true;
  session_boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  session_boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;

  omill::BoundaryFact module_boundary_fact = session_boundary_fact;
  module_boundary_fact.boundary_pc = 0x401600u;
  module_boundary_fact.continuation_pc = 0x401610u;
  module_boundary_fact.continuation_vip_pc = 0x401610u;
  omill::writeBoundaryFact(*Boundary, module_boundary_fact);

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  orchestrator.session().graph.boundary_facts_by_target[0x4016A0u].target_pc =
      0x4016A0u;
  orchestrator.session().graph.boundary_facts_by_target[0x4016A0u].boundary =
      session_boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x401610u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                                  size_t size) {
          if (size < 8)
            return false;
          const uint8_t bytes[8] = {0xE8, 0x0B, 0x00, 0x00,
                                    0x00, 0x90, 0x90, 0x90};
          std::memcpy(out, bytes, sizeof(bytes));
          for (size_t i = sizeof(bytes); i < size; ++i)
            out[i] = 0x90;
          return true;
        };
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401600u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401610u));
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryInheritsContinuationFromSessionBoundaryViaModuleBoundaryPc) {
  llvm::Module M("runtime_boundary_continuation_module_boundary_pc", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *NativeTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401897", M);
  auto *Continuation = addLiftedFunction(M, "blk_4018C3");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(NativeTarget, {Root->getArg(0), B.getInt64(0x401897),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact module_boundary_fact;
  module_boundary_fact.boundary_pc = 0x4017D4u;
  module_boundary_fact.native_target_pc = 0x401897u;
  omill::writeBoundaryFact(*NativeTarget, module_boundary_fact);

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact session_boundary_fact;
  session_boundary_fact.boundary_pc = 0x4017D4u;
  session_boundary_fact.native_target_pc = 0x4017D4u;
  session_boundary_fact.continuation_pc = 0x4018C3u;
  session_boundary_fact.reenters_vm = true;
  session_boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  session_boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x4017D4u].target_pc =
      0x4017D4u;
  orchestrator.session().graph.boundary_facts_by_target[0x4017D4u].boundary =
      session_boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);
  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x4018C3u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
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
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401897u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x4018C3u));
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryInheritsContinuationFromModuleBoundaryPcChain) {
  llvm::Module M("runtime_boundary_continuation_module_chain", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *NativeTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401897", M);
  auto *VmEnterTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_4017D4", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(NativeTarget, {Root->getArg(0), B.getInt64(0x401897),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact native_target_fact;
  native_target_fact.boundary_pc = 0x4017D4u;
  native_target_fact.native_target_pc = 0x401897u;
  omill::writeBoundaryFact(*NativeTarget, native_target_fact);

  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x4017D4u;
  vm_enter_fact.native_target_pc = 0x401897u;
  vm_enter_fact.continuation_pc = 0x4018C3u;
  vm_enter_fact.continuation_vip_pc = 0x4018C3u;
  vm_enter_fact.reenters_vm = true;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterTarget, vm_enter_fact);

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRuntime runtime(orchestrator);
  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x4018C3u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
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
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401897u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x4018C3u));
}

TEST_F(RuntimeTest,
       BuildFinalTailGraphPrefersRicherModuleBoundaryFactForNativeTarget) {
  llvm::Module M("runtime_tail_graph_module_boundary_preference", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *NativeTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401897", M);
  auto *VmEnterTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_4017D4", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(NativeTarget, {Root->getArg(0), B.getInt64(0x401897),
                                    Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::BoundaryFact native_target_fact;
  native_target_fact.boundary_pc = 0x4017D4u;
  native_target_fact.native_target_pc = 0x401897u;
  omill::writeBoundaryFact(*NativeTarget, native_target_fact);

  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x4017D4u;
  vm_enter_fact.native_target_pc = 0x401897u;
  vm_enter_fact.continuation_pc = 0x4018C3u;
  vm_enter_fact.reenters_vm = true;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterTarget, vm_enter_fact);

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);
  auto graph = runtime.buildFinalTailGraph(M);
  auto it = std::find_if(graph.nodes.begin(), graph.nodes.end(),
                         [&](const omill::FinalTailGraphNode &node) {
                           return node.target_pc == 0x401897u;
                         });
  ASSERT_NE(it, graph.nodes.end());
  EXPECT_EQ(it->kind, omill::FinalTailNodeKind::kModeledReentryBoundary);
  EXPECT_EQ(it->continuation_pc, std::optional<uint64_t>(0x4018C3u));
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryNormalizesBoundaryContinuationTargetBeforeLift) {
  llvm::Module M("runtime_boundary_continuation_normalized_target", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401600", M);
  auto *VmEnterPlaceholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_vm_enter_target_401610", M);
  omill::BoundaryFact vm_enter_fact;
  vm_enter_fact.boundary_pc = 0x401610u;
  vm_enter_fact.continuation_pc = 0x401610u;
  vm_enter_fact.continuation_vip_pc = 0x401610u;
  vm_enter_fact.is_vm_enter = true;
  vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
  vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
  omill::writeBoundaryFact(*VmEnterPlaceholder, vm_enter_fact);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401600),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401600u;
  boundary_fact.native_target_pc = 0x401600u;
  boundary_fact.continuation_pc = 0x401613u;
  boundary_fact.continuation_vip_pc = 0x401613u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401600u].target_pc =
      0x401600u;
  orchestrator.session().graph.boundary_facts_by_target[0x401600u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x401610u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) {
          return pc == 0x401613u ? 0x401610u : pc;
        };
        frontier_callbacks.can_decode_target = [](uint64_t pc) {
          return pc == 0x401610u;
        };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                                  size_t size) {
          if (size < 8)
            return false;
          const uint8_t bytes[8] = {0xE8, 0x4B, 0x00, 0x00,
                                    0x00, 0x90, 0x90, 0x90};
          std::memcpy(out, bytes, sizeof(bytes));
          for (size_t i = sizeof(bytes); i < size; ++i)
            out[i] = 0x90;
          return true;
        };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401600u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kKeptModeledBoundary);
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401613u));
  EXPECT_FALSE(llvm::is_contained(
      bundle->recovery_quality.lifted_boundary_continuations, 0x401613u));
  auto *BoundaryStub = M.getFunction("omill_native_target_401600");
  ASSERT_NE(BoundaryStub, nullptr);
  EXPECT_FALSE(BoundaryStub->isDeclaration());
  bool saw_continuation = false;
  for (auto &BB : *BoundaryStub) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || !CB->getCalledFunction())
        continue;
      if (CB->getCalledFunction()->getName() == VmEnterPlaceholder->getName())
        saw_continuation = true;
    }
  }
  EXPECT_TRUE(saw_continuation);
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryDrainsVmEnterSeededContinuationIntoBridge) {
  llvm::Module M("runtime_boundary_continuation_vm_enter_drain", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401700", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401700),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401700u;
  boundary_fact.native_target_pc = 0x401700u;
  boundary_fact.continuation_pc = 0x401710u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401700u].target_pc =
      0x401700u;
  orchestrator.session().graph.boundary_facts_by_target[0x401700u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  request.enable_gsd = true;

  unsigned cleanup_calls = 0;
  unsigned frontier_calls = 0;
  bool vm_enter_placeholder_seeded = false;
  bool native_bridge_materialized = false;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.run_final_output_cleanup = [&]() { ++cleanup_calls; };
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool, bool)
          -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x401710u)
          return std::nullopt;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.import_safety = omill::ChildImportClass::kBoundaryModeledChild;
        return artifact;
      };
  callbacks.import_vm_enter_child =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &,
          const omill::ChildImportPlan &, llvm::Function &placeholder) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        plan.eligibility = omill::ImportEligibility::kImportable;
        auto *imported = addLiftedFunction(M, "blk_401710");
        plan.imported_root = imported;
        return plan;
      };
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        ++frontier_calls;
        if (frontier_calls == 1) {
          auto *placeholder = llvm::Function::Create(
              liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
              "omill_vm_enter_target_401710", M);
          omill::BoundaryFact vm_enter_fact;
          vm_enter_fact.boundary_pc = 0x401710u;
          vm_enter_fact.is_vm_enter = true;
          vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
          vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
          omill::writeBoundaryFact(*placeholder, vm_enter_fact);

          auto &edge =
              orchestrator.session().graph.edge_facts_by_identity["vmenter:401710"];
          edge.identity = "vmenter:401710";
          edge.owner_function = "blk_401700";
          edge.target_pc = 0x401710u;
          edge.boundary = vm_enter_fact;
          edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
          edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
          edge.scheduling_class =
              omill::FrontierSchedulingClass::kTrustedLive;
          vm_enter_placeholder_seeded = true;
          return true;
        }
        if (frontier_calls == 2 && M.getFunction("blk_401710")) {
          auto *stub = M.getFunction("omill_native_target_401700");
          if (!stub)
            return false;
          if (!stub->isDeclaration())
            stub->deleteBody();
          auto *entry = llvm::BasicBlock::Create(Ctx, "entry", stub);
          llvm::IRBuilder<> B(entry);
          auto *native_target = llvm::Function::Create(
              stub->getFunctionType(), llvm::Function::ExternalLinkage,
              "native_sub_401700", M);
          auto *native_entry =
              llvm::BasicBlock::Create(Ctx, "entry", native_target);
          llvm::IRBuilder<> NB(native_entry);
          NB.CreateRet(native_target->getArg(2));
          auto *native_call = B.CreateCall(
              native_target,
              {stub->getArg(0),
               llvm::ConstantInt::get(
                   stub->getFunctionType()->getParamType(1), 0x401700u),
               stub->getArg(2)});
          auto *continuation = M.getFunction("blk_401710");
          auto *continuation_call = B.CreateCall(
              continuation,
              {stub->getArg(0),
               llvm::ConstantInt::get(
                   continuation->getFunctionType()->getParamType(1), 0x401710u),
               native_call});
          B.CreateRet(continuation_call);
          native_bridge_materialized = true;
          return true;
        }
        return false;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  EXPECT_TRUE(vm_enter_placeholder_seeded);
  EXPECT_TRUE(native_bridge_materialized);
  EXPECT_GE(frontier_calls, 2u);
  EXPECT_GE(cleanup_calls, 2u);

  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401700u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401710u));
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryUsesPreparedVmEnterChildSelectedRoot) {
  llvm::Module M("runtime_boundary_continuation_prepared_vm_enter_root", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401720", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401720),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401720u;
  boundary_fact.native_target_pc = 0x401720u;
  boundary_fact.continuation_pc = 0x401710u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401720u].target_pc =
      0x401720u;
  orchestrator.session().graph.boundary_facts_by_target[0x401720u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  request.enable_gsd = true;

  unsigned frontier_calls = 0;
  std::optional<uint64_t> observed_selected_root;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.run_final_output_cleanup = [] {};
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x401710u)
          return std::nullopt;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "define ptr @blk_401723(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  ret ptr %2\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401723 closed=true handler=blk_401723";
        return artifact;
      };
  callbacks.import_vm_enter_child =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &, llvm::Function &) {
        omill::ChildImportPlan plan;
        plan.target_pc = target_pc;
        observed_selected_root = artifact.selected_root_pc;
        EXPECT_EQ(observed_selected_root, std::optional<uint64_t>(0x401723u));
        plan.eligibility = omill::ImportEligibility::kImportable;
        plan.imported_root = addLiftedFunction(M, "blk_401723");
        return plan;
      };
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        ++frontier_calls;
        if (frontier_calls == 1) {
          auto *placeholder = llvm::Function::Create(
              liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
              "omill_vm_enter_target_401710", M);
          omill::BoundaryFact vm_enter_fact;
          vm_enter_fact.boundary_pc = 0x401710u;
          vm_enter_fact.is_vm_enter = true;
          vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
          vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
          omill::writeBoundaryFact(*placeholder, vm_enter_fact);

          auto &edge =
              orchestrator.session().graph.edge_facts_by_identity["vmenter:401710"];
          edge.identity = "vmenter:401710";
          edge.owner_function = "blk_401720";
          edge.target_pc = 0x401710u;
          edge.boundary = vm_enter_fact;
          edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
          edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
          edge.scheduling_class =
              omill::FrontierSchedulingClass::kTrustedLive;
          return true;
        }
        if (frontier_calls == 2 && M.getFunction("blk_401723")) {
          auto *stub = M.getFunction("omill_native_target_401720");
          if (!stub)
            return false;
          if (!stub->isDeclaration())
            stub->deleteBody();
          auto *entry = llvm::BasicBlock::Create(Ctx, "entry", stub);
          llvm::IRBuilder<> B(entry);
          auto *native_target = llvm::Function::Create(
              stub->getFunctionType(), llvm::Function::ExternalLinkage,
              "native_sub_401720", M);
          auto *native_entry =
              llvm::BasicBlock::Create(Ctx, "entry", native_target);
          llvm::IRBuilder<> NB(native_entry);
          NB.CreateRet(native_target->getArg(2));
          auto *native_call = B.CreateCall(
              native_target,
              {stub->getArg(0),
               llvm::ConstantInt::get(
                   stub->getFunctionType()->getParamType(1), 0x401720u),
               stub->getArg(2)});
          auto *continuation = M.getFunction("blk_401723");
          auto *continuation_call = B.CreateCall(
              continuation,
              {stub->getArg(0),
               llvm::ConstantInt::get(
                   continuation->getFunctionType()->getParamType(1), 0x401723u),
               native_call});
          B.CreateRet(continuation_call);
          return true;
        }
        return false;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  EXPECT_EQ(observed_selected_root, std::optional<uint64_t>(0x401723u));
  EXPECT_NE(M.getFunction("blk_401723"), nullptr);

  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401720u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryRetargetsPreparedVmEnterChildRootFromLocalizedContinuation) {
  llvm::Module M("runtime_boundary_continuation_retargeted_vm_enter_root", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401730", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401730),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401730u;
  boundary_fact.native_target_pc = 0x401730u;
  boundary_fact.continuation_pc = 0x401710u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401730u].target_pc =
      0x401730u;
  orchestrator.session().graph.boundary_facts_by_target[0x401730u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  request.enable_gsd = true;

  unsigned frontier_calls = 0;
  std::optional<uint64_t> observed_selected_root;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.run_final_output_cleanup = [] {};
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x401710u)
          return std::nullopt;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "define ptr @blk_401710(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %call = call ptr @blk_401723(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %call\n"
            "}\n"
            "define ptr @blk_401723(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  ret ptr %2\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401710 closed=true handler=blk_401710\n"
            "slice-handler blk_401710\n"
            "diag localized-continuation-call-edge caller=blk_401710 callee=blk_401723";
        return artifact;
      };
  callbacks.import_vm_enter_child =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &artifact,
          const omill::ChildImportPlan &preimport_plan, llvm::Function &) {
        EXPECT_EQ(target_pc, 0x401710u);
        observed_selected_root = artifact.selected_root_pc;
        EXPECT_EQ(observed_selected_root, std::optional<uint64_t>(0x401723u));
        EXPECT_EQ(preimport_plan.eligibility,
                  omill::ImportEligibility::kImportable);
        omill::ChildImportPlan plan = preimport_plan;
        plan.imported_root = addLiftedFunction(M, "blk_401723");
        return plan;
      };
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        ++frontier_calls;
        if (frontier_calls == 1) {
          auto *placeholder = llvm::Function::Create(
              liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
              "omill_vm_enter_target_401710", M);
          omill::BoundaryFact vm_enter_fact;
          vm_enter_fact.boundary_pc = 0x401710u;
          vm_enter_fact.is_vm_enter = true;
          vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
          vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
          omill::writeBoundaryFact(*placeholder, vm_enter_fact);

          auto &edge =
              orchestrator.session().graph.edge_facts_by_identity["vmenter:401710"];
          edge.identity = "vmenter:401710";
          edge.owner_function = "blk_401730";
          edge.target_pc = 0x401710u;
          edge.boundary = vm_enter_fact;
          edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
          edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
          edge.scheduling_class =
              omill::FrontierSchedulingClass::kTrustedLive;
          return true;
        }
        if (frontier_calls == 2 && M.getFunction("blk_401723")) {
          auto *stub = M.getFunction("omill_native_target_401730");
          if (!stub)
            return false;
          if (!stub->isDeclaration())
            stub->deleteBody();
          auto *entry = llvm::BasicBlock::Create(Ctx, "entry", stub);
          llvm::IRBuilder<> B(entry);
          auto *native_target = llvm::Function::Create(
              stub->getFunctionType(), llvm::Function::ExternalLinkage,
              "native_sub_401730", M);
          auto *native_entry =
              llvm::BasicBlock::Create(Ctx, "entry", native_target);
          llvm::IRBuilder<> NB(native_entry);
          NB.CreateRet(native_target->getArg(2));
          auto *native_call = B.CreateCall(
              native_target,
              {stub->getArg(0),
               llvm::ConstantInt::get(
                   stub->getFunctionType()->getParamType(1), 0x401730u),
               stub->getArg(2)});
          auto *continuation = M.getFunction("blk_401723");
          auto *continuation_call = B.CreateCall(
              continuation,
              {stub->getArg(0),
               llvm::ConstantInt::get(
                   continuation->getFunctionType()->getParamType(1), 0x401723u),
               native_call});
          B.CreateRet(continuation_call);
          return true;
        }
        return false;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  EXPECT_EQ(observed_selected_root, std::optional<uint64_t>(0x401723u));

  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401730u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
}

TEST_F(RuntimeTest, BoundaryTailRecoveryReportsVmEnterChildFailureReason) {
  llvm::Module M("runtime_boundary_continuation_vm_enter_failure_detail", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401760", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401760),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::BoundaryFact boundary_fact;
  boundary_fact.boundary_pc = 0x401760u;
  boundary_fact.native_target_pc = 0x401760u;
  boundary_fact.continuation_pc = 0x401770u;
  boundary_fact.reenters_vm = true;
  boundary_fact.exit_disposition =
      omill::BoundaryDisposition::kVmExitNativeCallReenter;
  boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
  orchestrator.session().graph.boundary_facts_by_target[0x401760u].target_pc =
      0x401760u;
  orchestrator.session().graph.boundary_facts_by_target[0x401760u].boundary =
      boundary_fact;

  omill::DevirtualizationRuntime runtime(orchestrator);
  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  request.enable_gsd = true;

  unsigned frontier_calls = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.run_final_output_cleanup = [] {};
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x401770u)
          return std::nullopt;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "declare ptr @__remill_function_call(ptr, i64, ptr)\n"
            "define ptr @blk_401770(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %call = call ptr @__remill_function_call(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %call\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401770 closed=true handler=blk_401770\n"
            "Devirtualization invariant violation: unresolved_dispatch_intrinsics";
        return artifact;
      };
  callbacks.import_vm_enter_child =
      [&](uint64_t target_pc, const omill::ChildLiftArtifact &,
          const omill::ChildImportPlan &preimport_plan, llvm::Function &) {
        EXPECT_EQ(target_pc, 0x401770u);
        return preimport_plan;
      };
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        ++frontier_calls;
        if (frontier_calls != 1)
          return false;
        auto *placeholder = llvm::Function::Create(
            liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
            "omill_vm_enter_target_401770", M);
        omill::BoundaryFact vm_enter_fact;
        vm_enter_fact.boundary_pc = 0x401770u;
        vm_enter_fact.is_vm_enter = true;
        vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
        vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
        omill::writeBoundaryFact(*placeholder, vm_enter_fact);

        auto &edge =
            orchestrator.session().graph.edge_facts_by_identity["vmenter:401770"];
        edge.identity = "vmenter:401770";
        edge.owner_function = "blk_401760";
        edge.target_pc = 0x401770u;
        edge.boundary = vm_enter_fact;
        edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
        edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
        edge.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;
        return true;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401760u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kKeptModeledBoundary);
  EXPECT_EQ(result_it->detail,
            "vm_enter_child:runtime_leak:remill_function_call+"
            "unresolved_dispatch_intrinsics");
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryCachesNonImportableVmEnterChildAcrossBoundaries) {
  llvm::Module M("runtime_boundary_continuation_vm_enter_cached_failure", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *BoundaryA = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401760", M);
  auto *BoundaryB = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401761", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call_a =
        B.CreateCall(BoundaryA, {Root->getArg(0), B.getInt64(0x401760),
                                 Root->getArg(2)});
    auto *call_b =
        B.CreateCall(BoundaryB, {Root->getArg(0), B.getInt64(0x401761),
                                 call_a});
    B.CreateRet(call_b);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  for (uint64_t boundary_pc : {0x401760u, 0x401761u}) {
    omill::BoundaryFact boundary_fact;
    boundary_fact.boundary_pc = boundary_pc;
    boundary_fact.native_target_pc = boundary_pc;
    boundary_fact.continuation_pc = 0x401770u;
    boundary_fact.reenters_vm = true;
    boundary_fact.exit_disposition =
        omill::BoundaryDisposition::kVmExitNativeCallReenter;
    boundary_fact.kind = omill::BoundaryKind::kNativeBoundary;
    orchestrator.session().graph.boundary_facts_by_target[boundary_pc].target_pc =
        boundary_pc;
    orchestrator.session().graph.boundary_facts_by_target[boundary_pc].boundary =
        boundary_fact;
  }

  omill::DevirtualizationRuntime runtime(orchestrator);
  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;
  request.enable_gsd = true;

  unsigned frontier_calls = 0;
  unsigned lift_calls = 0;
  omill::OutputRecoveryCallbacks callbacks;
  callbacks.run_final_output_cleanup = [] {};
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x401770u)
          return std::nullopt;
        ++lift_calls;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "define ptr @blk_401770(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %call = call ptr @blk_401780(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %call\n"
            "}\n"
            "define ptr @blk_401780(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  ret ptr %2\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401770 closed=true handler=blk_401770";
        return artifact;
      };
  callbacks.import_vm_enter_child =
      [&](uint64_t, const omill::ChildLiftArtifact &,
          const omill::ChildImportPlan &, llvm::Function &) {
        ADD_FAILURE() << "non-importable vm-enter child should not reach adapter";
        return omill::ChildImportPlan{};
      };
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        ++frontier_calls;
        auto *placeholder = M.getFunction("omill_vm_enter_target_401770");
        if (!placeholder) {
          placeholder = llvm::Function::Create(
              liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
              "omill_vm_enter_target_401770", M);
          omill::BoundaryFact vm_enter_fact;
          vm_enter_fact.boundary_pc = 0x401770u;
          vm_enter_fact.is_vm_enter = true;
          vm_enter_fact.exit_disposition = omill::BoundaryDisposition::kVmEnter;
          vm_enter_fact.kind = omill::BoundaryKind::kVmEnterBoundary;
          omill::writeBoundaryFact(*placeholder, vm_enter_fact);

          auto &edge =
              orchestrator.session().graph.edge_facts_by_identity["vmenter:401770"];
          edge.identity = "vmenter:401770";
          edge.owner_function = "blk_401760";
          edge.target_pc = 0x401770u;
          edge.boundary = vm_enter_fact;
          edge.kind = omill::FrontierWorkKind::kVmEnterBoundary;
          edge.status = omill::FrontierWorkStatus::kClassifiedVmEnter;
          edge.scheduling_class = omill::FrontierSchedulingClass::kTrustedLive;
        }
        return true;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  EXPECT_EQ(lift_calls, 1u);
  auto results = llvm::make_filter_range(
      bundle->boundary_recovery_results,
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401760u || result.target_pc == 0x401761u;
      });
  unsigned seen = 0;
  for (const auto &result : results) {
    ++seen;
    EXPECT_EQ(result.disposition,
              omill::BoundaryTailRecoveryDisposition::kKeptModeledBoundary);
    EXPECT_EQ(result.detail, "vm_enter_child:terminal_modeled_vm_enter_child");
  }
  EXPECT_EQ(seen, 2u);
  EXPECT_GT(frontier_calls, 0u);
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

TEST_F(RuntimeTest,
       FinalTailGraphProjectionPreservesNestedBoundaryDescendantsInAbi) {
  llvm::Module Source("runtime_tail_graph_source", Ctx);
  auto *SourceRoot = addLiftedFunction(Source, "sub_401000");
  SourceRoot->addFnAttr("omill.output_root");
  auto *SourceMid = addLiftedFunction(Source, "blk_401060");
  auto *SourceChild = addLiftedFunction(Source, "execchild_sub_401065");
  auto *BoundaryA = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_boundary_401235", Source);
  auto *BoundaryB = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_boundary_401234", Source);

  SourceRoot->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&SourceRoot->getEntryBlock());
    auto *call =
        B.CreateCall(SourceMid, {SourceRoot->getArg(0), B.getInt64(0x401060),
                                 SourceRoot->getArg(2)});
    B.CreateRet(call);
  }

  SourceMid->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&SourceMid->getEntryBlock());
    auto *call = B.CreateCall(SourceChild,
                              {SourceMid->getArg(0), B.getInt64(0x401065),
                               SourceMid->getArg(2)});
    B.CreateRet(call);
  }

  SourceChild->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&SourceChild->getEntryBlock());
    auto *first = B.CreateCall(
        BoundaryA, {SourceChild->getArg(0), B.getInt64(0x401235),
                    SourceChild->getArg(2)});
    auto *second = B.CreateCall(
        BoundaryB, {SourceChild->getArg(0), B.getInt64(0x401234), first});
    B.CreateRet(second);
  }

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  auto graph = runtime.buildFinalTailGraph(Source);
  EXPECT_EQ(graph.nodes.size(), 2u);
  EXPECT_TRUE(std::any_of(graph.edges.begin(), graph.edges.end(),
                          [](const omill::FinalTailGraphEdge &edge) {
                            return edge.source_pc &&
                                   *edge.source_pc == 0x401065u &&
                                   edge.target_pc == 0x401235u;
                          }));
  EXPECT_TRUE(std::any_of(graph.edges.begin(), graph.edges.end(),
                          [](const omill::FinalTailGraphEdge &edge) {
                            return edge.source_pc &&
                                   *edge.source_pc == 0x401065u &&
                                   edge.target_pc == 0x401234u;
                          }));

  llvm::Module Abi("runtime_tail_graph_dest", Ctx);
  auto *AbiRoot = addLiftedFunction(Abi, "sub_401000");
  AbiRoot->addFnAttr("omill.output_root");
  auto *AbiMid = addLiftedFunction(Abi, "blk_401060");
  auto *AbiChildDecl = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage, "blk_401065", Abi);

  AbiRoot->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&AbiRoot->getEntryBlock());
    auto *call =
        B.CreateCall(AbiMid, {AbiRoot->getArg(0), B.getInt64(0x401060),
                              AbiRoot->getArg(2)});
    B.CreateRet(call);
  }

  AbiMid->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&AbiMid->getEntryBlock());
    auto *call =
        B.CreateCall(AbiChildDecl, {AbiMid->getArg(0), B.getInt64(0x401065),
                                    AbiMid->getArg(2)});
    B.CreateRet(call);
  }

  ASSERT_TRUE(runtime.projectFinalTailGraphIntoAbiModule(Abi, graph));
  EXPECT_NE(Abi.getFunction("omill_native_boundary_401235"), nullptr);
  EXPECT_NE(Abi.getFunction("omill_native_boundary_401234"), nullptr);

  auto *ProjectedChild = Abi.getFunction("blk_401065");
  ASSERT_NE(ProjectedChild, nullptr);
  auto targets_attr =
      ProjectedChild->getFnAttribute("omill.final_tail_graph_targets");
  ASSERT_TRUE(targets_attr.isValid());
  EXPECT_EQ(targets_attr.getValueAsString(), "401234,401235");

  auto roundtrip_graph = runtime.buildFinalTailGraph(Abi);
  EXPECT_TRUE(std::any_of(roundtrip_graph.nodes.begin(),
                          roundtrip_graph.nodes.end(),
                          [](const omill::FinalTailGraphNode &node) {
                            return node.target_pc == 0x401234u;
                          }));
  EXPECT_TRUE(std::any_of(roundtrip_graph.nodes.begin(),
                          roundtrip_graph.nodes.end(),
                          [](const omill::FinalTailGraphNode &node) {
                            return node.target_pc == 0x401235u;
                          }));
}

TEST_F(RuntimeTest,
       RefineFinalTailGraphClassifiesBoundaryNodesFromReplayAndReentryProof) {
  llvm::Module M("runtime_tail_graph_boundary_refine", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

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
  omill::FinalTailGraph graph;
  graph.nodes.push_back({0x401400u, "omill_native_target_401400",
                         omill::FinalTailNodeKind::kRetryableBoundary, ""});
  graph.nodes.push_back({0x401434u, "omill_native_boundary_401434",
                         omill::FinalTailNodeKind::kRetryableBoundary, ""});
  graph.nodes.push_back({0x401435u, "omill_native_boundary_401435",
                         omill::FinalTailNodeKind::kRetryableBoundary, ""});

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        if (target_pc == 0x401434u) {
          artifact.ir_text =
              "define ptr @sub_401434(ptr %0, i64 %1, ptr %2) {\n"
              "entry:\n"
              "  br label %tail\n"
              "tail:\n"
              "  br label %tail\n"
              "}\n";
          return artifact;
        }
        if (target_pc == 0x401435u) {
          artifact.ir_text =
              "declare ptr @__remill_function_call(ptr, i64, ptr)\n"
              "define ptr @sub_401435(ptr %0, i64 %1, ptr %2) {\n"
              "entry:\n"
              "  %call = call ptr @__remill_function_call(ptr %0, i64 %1, ptr %2)\n"
              "  ret ptr %call\n"
              "}\n";
          return artifact;
        }
        return std::nullopt;
      };

  ASSERT_TRUE(runtime.refineFinalTailGraphWithBoundaryReplay(M, graph, callbacks,
                                                             false));
  auto find_node = [&](uint64_t pc) -> const omill::FinalTailGraphNode * {
    auto it = std::find_if(graph.nodes.begin(), graph.nodes.end(),
                           [&](const omill::FinalTailGraphNode &node) {
                             return node.target_pc == pc;
                           });
    return it == graph.nodes.end() ? nullptr : &*it;
  };

  ASSERT_NE(find_node(0x401400u), nullptr);
  EXPECT_EQ(find_node(0x401400u)->kind,
            omill::FinalTailNodeKind::kModeledReentryBoundary);
  ASSERT_NE(find_node(0x401434u), nullptr);
  EXPECT_EQ(find_node(0x401434u)->kind,
            omill::FinalTailNodeKind::kTerminalModeledBoundary);
  ASSERT_NE(find_node(0x401435u), nullptr);
  EXPECT_EQ(find_node(0x401435u)->kind,
            omill::FinalTailNodeKind::kHardRejectedBoundary);
}

TEST_F(RuntimeTest,
       RefineFinalTailGraphReplaysRetryableNativeTargetWithoutContinuation) {
  llvm::Module M("runtime_tail_graph_native_target_replay", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalTailGraph graph;
  graph.nodes.push_back({0x4017dd4u, "omill_native_target_4017dd4",
                         omill::FinalTailNodeKind::kRetryableBoundary, ""});

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x4017dd4u)
          return std::nullopt;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "define ptr @sub_4017dd4(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  br label %tail\n"
            "tail:\n"
            "  br label %tail\n"
            "}\n";
        return artifact;
      };

  ASSERT_TRUE(runtime.refineFinalTailGraphWithBoundaryReplay(M, graph, callbacks,
                                                             false));
  ASSERT_EQ(graph.nodes.size(), 1u);
  EXPECT_EQ(graph.nodes.front().target_pc, 0x4017dd4u);
  EXPECT_EQ(graph.nodes.front().kind,
            omill::FinalTailNodeKind::kTerminalModeledBoundary);
  EXPECT_EQ(graph.nodes.front().detail, "terminal_modeled_boundary");
}

TEST_F(
    RuntimeTest,
    RefineFinalTailGraphPromotesJumpTailBoundaryToModeledReentryWhenModelProvidesUniqueContinuation) {
  llvm::Module M("runtime_tail_graph_jump_tail_reentry", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalTailGraph graph;
  graph.nodes.push_back({0x401597u, "omill_native_target_401597",
                         omill::FinalTailNodeKind::kRetryableBoundary, ""});

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.lift_child_target =
      [&](uint64_t target_pc, bool, bool, bool,
          bool) -> std::optional<omill::ChildLiftArtifact> {
        if (target_pc != 0x401597u)
          return std::nullopt;
        omill::ChildLiftArtifact artifact;
        artifact.target_pc = target_pc;
        artifact.ir_text =
            "declare ptr @__remill_jump(ptr, i64, ptr)\n"
            "define ptr @sub_401597(ptr %0, i64 %1, ptr %2) {\n"
            "entry:\n"
            "  %jump = call ptr @__remill_jump(ptr %0, i64 %1, ptr %2)\n"
            "  ret ptr %jump\n"
            "}\n";
        artifact.model_text =
            "root-slice root=0x401597 reachable=2 frontier=1 closed=false\n"
            "frontier target=0x401610 reason=jump_tail\n";
        return artifact;
      };

  ASSERT_TRUE(runtime.refineFinalTailGraphWithBoundaryReplay(M, graph, callbacks,
                                                             false));
  ASSERT_EQ(graph.nodes.size(), 1u);
  EXPECT_EQ(graph.nodes.front().kind,
            omill::FinalTailNodeKind::kModeledReentryBoundary);
  EXPECT_EQ(graph.nodes.front().detail, "jump_tail_modeled_reentry_boundary");
  EXPECT_EQ(graph.nodes.front().continuation_pc, std::optional<uint64_t>(0x401610u));
}

TEST_F(RuntimeTest,
       BuildFinalTailGraphTreatsNativeTargetPlaceholdersWithoutReentryEvidenceAsRetryable) {
  llvm::Module M("runtime_tail_graph_native_target", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *NativeTarget = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_4017dd4", M);

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call = B.CreateCall(
        NativeTarget, {Root->getArg(0), B.getInt64(0x4017dd4),
                       Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator;
  omill::DevirtualizationRuntime runtime(orchestrator);
  auto graph = runtime.buildFinalTailGraph(M);
  auto it = std::find_if(graph.nodes.begin(), graph.nodes.end(),
                         [&](const omill::FinalTailGraphNode &node) {
                           return node.target_pc == 0x4017dd4u;
                         });
  ASSERT_NE(it, graph.nodes.end());
  EXPECT_EQ(it->kind, omill::FinalTailNodeKind::kRetryableBoundary);
  EXPECT_EQ(it->detail, "retryable_boundary");
}

TEST_F(RuntimeTest,
       BoundaryTailRecoveryUsesTailGraphContinuationWhenBoundaryFactIsMissing) {
  llvm::Module M("runtime_boundary_tail_graph_continuation", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Boundary = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_native_target_401597", M);
  auto *Continuation = addLiftedFunction(M, "blk_401610");

  Root->getEntryBlock().getTerminator()->eraseFromParent();
  {
    llvm::IRBuilder<> B(&Root->getEntryBlock());
    auto *call =
        B.CreateCall(Boundary, {Root->getArg(0), B.getInt64(0x401597),
                                Root->getArg(2)});
    B.CreateRet(call);
  }

  omill::DevirtualizationOrchestrator orchestrator(
      {}, std::make_shared<omill::IterativeLiftingSession>());
  omill::DevirtualizationRuntime runtime(orchestrator);

  omill::FinalTailGraph graph;
  graph.nodes.push_back({0x401597u, "omill_native_target_401597",
                         omill::FinalTailNodeKind::kModeledReentryBoundary,
                         "jump_tail_modeled_reentry_boundary", 0x401610u});
  ASSERT_TRUE(runtime.projectFinalTailGraphIntoAbiModule(M, graph));

  omill::FinalStateRecoveryRequest request;
  request.no_abi = true;
  request.enabled = true;

  omill::OutputRecoveryCallbacks callbacks;
  callbacks.advance_session_owned_frontier_work =
      [&](omill::FrontierDiscoveryPhase, llvm::StringRef) {
        omill::FrontierCallbacks frontier_callbacks;
        frontier_callbacks.is_code_address = [](uint64_t) { return true; };
        frontier_callbacks.has_defined_target = [](uint64_t pc) {
          return pc == 0x401610u;
        };
        frontier_callbacks.normalize_target_pc = [](uint64_t pc) { return pc; };
        frontier_callbacks.read_target_bytes = [](uint64_t, uint8_t *out,
                                                  size_t size) {
          if (size < 8)
            return false;
          const uint8_t bytes[8] = {0xE8, 0x14, 0x00, 0x00,
                                    0x00, 0x90, 0x90, 0x90};
          std::memcpy(out, bytes, sizeof(bytes));
          for (size_t i = sizeof(bytes); i < size; ++i)
            out[i] = 0x90;
          return true;
        };
        frontier_callbacks.can_decode_target = [](uint64_t) { return true; };
        auto *fake_lifter =
            reinterpret_cast<omill::BlockLifter *>(static_cast<uintptr_t>(0x1));
        auto summary = orchestrator.advanceFrontierWork(
            M, *fake_lifter, *orchestrator.session().iterative_session,
            frontier_callbacks);
        return summary.changed;
      };

  auto bundle = runtime.runBoundaryTailRecovery(M, request, callbacks);
  ASSERT_TRUE(bundle.has_value());
  auto result_it = std::find_if(
      bundle->boundary_recovery_results.begin(),
      bundle->boundary_recovery_results.end(),
      [](const omill::BoundaryTailRecoveryActionResult &result) {
        return result.target_pc == 0x401597u;
      });
  ASSERT_NE(result_it, bundle->boundary_recovery_results.end());
  EXPECT_EQ(result_it->disposition,
            omill::BoundaryTailRecoveryDisposition::kContinuationLifted);
  EXPECT_EQ(result_it->continuation_pc, std::optional<uint64_t>(0x401610u));
  EXPECT_TRUE(llvm::is_contained(
      bundle->recovery_quality.lifted_boundary_continuations, 0x401610u));
}

}  // namespace
