#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Devirtualization/Orchestrator.h"
#include "omill/Devirtualization/Runtime.h"

#include <gtest/gtest.h>

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

namespace {

class ProtectorModelTest : public ::testing::Test {
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
};

TEST_F(ProtectorModelTest,
       BuildProtectorModelClassifiesInvalidatedExecutableAsQuarantinedArm) {
  omill::DevirtualizationOrchestrator Orchestrator;
  auto &Trusted =
      Orchestrator.session().graph.edge_facts_by_identity["closure:trusted"];
  Trusted.identity = "closure:trusted";
  Trusted.owner_function = "sub_401000";
  Trusted.site_index = 0;
  Trusted.site_pc = 0x401000u;
  Trusted.target_pc = 0x401260u;
  Trusted.boundary = omill::BoundaryFact{};
  Trusted.boundary->boundary_pc = 0x401260u;
  Trusted.boundary->exit_disposition = omill::BoundaryDisposition::kVmEnter;
  Trusted.boundary->is_vm_enter = true;
  Trusted.kind = omill::FrontierWorkKind::kVmEnterBoundary;

  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["closure:test-edge"];
  Edge.identity = "closure:test-edge";
  Edge.owner_function = "sub_401000";
  Edge.site_index = 0;
  Edge.site_pc = 0x401000u;
  Edge.target_pc = 0x401230u;
  Edge.executable_target = omill::ExecutableTargetFact{};
  Edge.executable_target->raw_target_pc = 0x401230u;
  Edge.executable_target->invalidated_executable_entry = true;

  auto Model = Orchestrator.buildProtectorModel();
  ASSERT_EQ(Model.continuation_candidates.size(), 2u);
  auto It = std::find_if(
      Model.continuation_candidates.begin(), Model.continuation_candidates.end(),
      [](const auto &candidate) {
        return candidate.edge_identity == "closure:test-edge";
      });
  ASSERT_NE(It, Model.continuation_candidates.end());
  EXPECT_EQ(It->provenance,
            omill::ContinuationProvenance::kInvalidatedExecutableEntry);
  EXPECT_EQ(It->liveness,
            omill::ContinuationLiveness::kQuarantined);
  EXPECT_EQ(Model.dispatcher_families.size(), 1u);
  EXPECT_EQ(Model.dispatcher_families.front().anchor_handler_name, "sub_401000");
}

TEST_F(ProtectorModelTest,
       RuntimeValidationReportIncludesExecutablePlaceholderAndQuarantinedArm) {
  llvm::Module M("protector_report", Ctx);
  auto *Root = addLiftedFunction(M, "sub_401000");
  Root->addFnAttr("omill.output_root");
  auto *Placeholder = llvm::Function::Create(
      liftedFnTy(Ctx), llvm::Function::ExternalLinkage,
      "omill_executable_target_401230", M);

  auto &Entry = Root->getEntryBlock();
  Entry.getTerminator()->eraseFromParent();
  llvm::IRBuilder<> B(&Entry);
  B.CreateCall(Placeholder, {Root->getArg(0), B.getInt64(0x401230),
                             Root->getArg(2)});
  B.CreateRet(Root->getArg(2));

  omill::DevirtualizationOrchestrator Orchestrator;
  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["closure:test-edge"];
  Edge.identity = "closure:test-edge";
  Edge.owner_function = "sub_401000";
  Edge.target_pc = 0x401230u;
  Edge.executable_target = omill::ExecutableTargetFact{};
  Edge.executable_target->raw_target_pc = 0x401230u;
  Edge.executable_target->invalidated_executable_entry = true;
  Edge.continuation_confidence = omill::ContinuationConfidence::kDeadArmSuspect;
  Edge.continuation_liveness = omill::ContinuationLiveness::kQuarantined;
  Edge.scheduling_class = omill::FrontierSchedulingClass::kQuarantinedSelectorArm;

  omill::DevirtualizationRuntime Runtime(Orchestrator);
  auto Report = Runtime.buildValidationReport(M);

  EXPECT_GE(Report.counts_by_class["executable_placeholder"], 1u);
  EXPECT_GE(Report.counts_by_class["quarantined_selector_arm"], 1u);
}

TEST_F(ProtectorModelTest,
       BuildProtectorModelSynthesizesImportableProofForExactFallthrough) {
  omill::DevirtualizationOrchestrator Orchestrator;
  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["closure:fallthrough"];
  Edge.identity = "closure:fallthrough";
  Edge.owner_function = "sub_401000";
  Edge.site_index = 0;
  Edge.site_pc = 0x401000u;
  Edge.target_pc = 0x401230u;
  Edge.executable_target = omill::ExecutableTargetFact{};
  Edge.executable_target->raw_target_pc = 0x401230u;
  Edge.executable_target->effective_target_pc = 0x401230u;
  Edge.executable_target->exact_fallthrough_target = 0x401230u;

  auto Model = Orchestrator.buildProtectorModel();
  ASSERT_EQ(Model.continuation_candidates.size(), 1u);
  ASSERT_TRUE(Model.continuation_candidates.front().proof.has_value());
  const auto &Proof = *Model.continuation_candidates.front().proof;
  EXPECT_EQ(Proof.resolution_kind,
            omill::ContinuationResolutionKind::kExactFallthrough);
  EXPECT_EQ(Proof.import_disposition,
            omill::ContinuationImportDisposition::kImportable);
  ASSERT_TRUE(Proof.selected_root_import_class.has_value());
  EXPECT_EQ(*Proof.selected_root_import_class,
            omill::ChildImportClass::kTrustedTerminalEntry);
}

TEST_F(ProtectorModelTest,
       BuildProtectorModelKeepsInvalidatedExecutableProofRejectedByDefault) {
  omill::DevirtualizationOrchestrator Orchestrator;
  auto &Edge =
      Orchestrator.session().graph.edge_facts_by_identity["closure:invalidated"];
  Edge.identity = "closure:invalidated";
  Edge.owner_function = "sub_401000";
  Edge.site_index = 0;
  Edge.site_pc = 0x401000u;
  Edge.target_pc = 0x401230u;
  Edge.executable_target = omill::ExecutableTargetFact{};
  Edge.executable_target->raw_target_pc = 0x401230u;
  Edge.executable_target->invalidated_executable_entry = true;

  auto Model = Orchestrator.buildProtectorModel();
  ASSERT_EQ(Model.continuation_candidates.size(), 1u);
  ASSERT_TRUE(Model.continuation_candidates.front().proof.has_value());
  const auto &Proof = *Model.continuation_candidates.front().proof;
  EXPECT_EQ(Proof.resolution_kind,
            omill::ContinuationResolutionKind::kInvalidatedExecutableEntry);
  EXPECT_EQ(Proof.import_disposition,
            omill::ContinuationImportDisposition::kRejected);
}

}  // namespace
