#include "omill/Devirtualization/BinaryRegionReconstructor.h"
#include "omill/Devirtualization/ContinuationResolver.h"

#include <gtest/gtest.h>

#include <algorithm>

namespace {

TEST(BinaryRegionReconstructorTest,
     RestatesLocalCfgUsingProofSuppliedOutgoingEdges) {
  omill::BinaryRegionReconstructor reconstructor;
  omill::BinaryRegionReconstructionRequest request;
  request.root_target_pc = 0x401230u;

  omill::LearnedOutgoingEdge learned;
  learned.source_pc = 0x401230u;
  learned.target_pc = 0x401250u;
  learned.restatement_kind = omill::EdgeRestatementKind::kProofSupplied;
  learned.resolution_status = omill::EdgeResolutionStatus::kResolved;
  request.learned_edges_by_source[0x401230u] = {learned};

  omill::FrontierCallbacks callbacks;
  callbacks.read_target_bytes = [](uint64_t, uint8_t *, size_t) {
    return false;
  };

  auto snapshot = reconstructor.reconstruct(request, callbacks);
  ASSERT_GE(snapshot.blocks_by_pc.size(), 1u);
  auto it = snapshot.blocks_by_pc.find(0x401230u);
  ASSERT_NE(it, snapshot.blocks_by_pc.end());
  ASSERT_EQ(it->second.outgoing_edges.size(), 1u);
  EXPECT_EQ(it->second.outgoing_edges.front().target_pc, 0x401250u);
  EXPECT_EQ(it->second.outgoing_edges.front().restatement_kind,
            omill::EdgeRestatementKind::kProofSupplied);
}

TEST(BinaryRegionReconstructorTest,
     PreservesExactFallthroughEvidenceFromTrustedContinuation) {
  omill::BinaryRegionReconstructor reconstructor;
  omill::BinaryRegionReconstructionRequest request;
  request.root_target_pc = 0x401230u;
  request.proof = omill::ContinuationProof{};
  request.proof->raw_target_pc = 0x401230u;
  request.proof->resolution_kind =
      omill::ContinuationResolutionKind::kExactFallthrough;
  request.proof->is_exact_fallthrough = true;

  omill::FrontierCallbacks callbacks;
  callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    summary.is_control_flow = false;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };
  callbacks.is_executable_target = [](uint64_t) { return true; };

  auto snapshot = reconstructor.reconstruct(request, callbacks);
  EXPECT_TRUE(snapshot.preserved_exact_call_fallthrough);
  EXPECT_FALSE(snapshot.visited_block_pcs.empty());
}

TEST(BinaryRegionReconstructorTest,
     PreservesExactFallthroughEvidenceFromBinaryCallbackWithoutExactProof) {
  omill::BinaryRegionReconstructor reconstructor;
  omill::BinaryRegionReconstructionRequest request;
  request.root_target_pc = 0x401230u;
  request.proof = omill::ContinuationProof{};
  request.proof->raw_target_pc = 0x401230u;
  request.proof->resolution_kind =
      omill::ContinuationResolutionKind::kTerminalModeled;
  request.proof->import_disposition =
      omill::ContinuationImportDisposition::kRetryable;

  omill::FrontierCallbacks callbacks;
  callbacks.can_decode_target = [](uint64_t) { return false; };
  callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    summary.is_control_flow = false;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };
  callbacks.is_exact_call_fallthrough_target = [](uint64_t pc) {
    return pc == 0x401230u;
  };
  callbacks.is_executable_target = [](uint64_t) { return true; };

  auto snapshot = reconstructor.reconstruct(request, callbacks);
  EXPECT_TRUE(snapshot.preserved_exact_call_fallthrough);
  EXPECT_FALSE(snapshot.visited_block_pcs.empty());
}

TEST(BinaryRegionReconstructorTest,
     RecursiveDescentReturnsThroughCallFrameInsteadOfDirectFallthrough) {
  omill::BinaryRegionReconstructor reconstructor;
  omill::BinaryRegionReconstructionRequest request;
  request.root_target_pc = 0x401000u;

  omill::FrontierCallbacks callbacks;
  callbacks.read_target_bytes = [](uint64_t pc, uint8_t *out, size_t size) {
    if (!size)
      return false;
    std::fill(out, out + size, 0x90);
    if (pc == 0x401000u) {
      out[0] = 0xE8;
      out[1] = 0x0B;
      out[2] = 0x00;
      out[3] = 0x00;
      out[4] = 0x00;
      return true;
    }
    if (pc == 0x401010u) {
      out[0] = 0xC3;
      return true;
    }
    if (pc == 0x401005u) {
      out[0] = 0x90;
      return true;
    }
    return false;
  };
  callbacks.can_decode_target = [](uint64_t pc) {
    return pc == 0x401000u || pc == 0x401010u || pc == 0x401005u;
  };
  callbacks.is_executable_target = [](uint64_t pc) {
    return pc == 0x401000u || pc == 0x401010u || pc == 0x401005u;
  };

  auto snapshot = reconstructor.reconstruct(request, callbacks);
  auto root_it = snapshot.blocks_by_pc.find(0x401000u);
  ASSERT_NE(root_it, snapshot.blocks_by_pc.end());
  ASSERT_EQ(root_it->second.outgoing_edges.size(), 1u);
  EXPECT_EQ(root_it->second.outgoing_edges.front().target_pc,
            std::optional<uint64_t>(0x401010u));

  auto callee_it = snapshot.blocks_by_pc.find(0x401010u);
  ASSERT_NE(callee_it, snapshot.blocks_by_pc.end());
  ASSERT_EQ(callee_it->second.outgoing_edges.size(), 1u);
  EXPECT_EQ(callee_it->second.outgoing_edges.front().target_pc,
            std::optional<uint64_t>(0x401005u));
  EXPECT_EQ(callee_it->second.outgoing_edges.front().restatement_kind,
            omill::EdgeRestatementKind::kBinaryDirect);
}

TEST(BinaryRegionReconstructorTest,
     ReturnAddressControlledRetRedirectsToEffectiveReturnTarget) {
  omill::BinaryRegionReconstructor reconstructor;
  omill::BinaryRegionReconstructionRequest request;
  request.root_target_pc = 0x401010u;
  omill::DescentReturnAddressState state;
  state.call_site_pc = 0x401000u;
  state.original_return_pc = 0x401005u;
  state.effective_return_pc = 0x401099u;
  state.return_slot_id = 7u;
  state.control_kind =
      omill::VirtualReturnAddressControlKind::kRedirectedConstant;
  state.suppresses_normal_fallthrough = true;
  request.initial_return_address_state = state;

  omill::FrontierCallbacks callbacks;
  callbacks.read_target_bytes = [](uint64_t pc, uint8_t *out, size_t size) {
    if (!size)
      return false;
    std::fill(out, out + size, 0x90);
    if (pc == 0x401010u || pc == 0x401099u) {
      out[0] = (pc == 0x401010u) ? 0xC3 : 0x90;
      return true;
    }
    return false;
  };
  callbacks.can_decode_target = [](uint64_t pc) {
    return pc == 0x401010u || pc == 0x401099u;
  };
  callbacks.is_executable_target = [](uint64_t pc) {
    return pc == 0x401010u || pc == 0x401099u;
  };

  auto snapshot = reconstructor.reconstruct(request, callbacks);
  auto it = snapshot.blocks_by_pc.find(0x401010u);
  ASSERT_NE(it, snapshot.blocks_by_pc.end());
  ASSERT_EQ(it->second.outgoing_edges.size(), 1u);
  EXPECT_EQ(it->second.outgoing_edges.front().target_pc,
            std::optional<uint64_t>(0x401099u));
  EXPECT_TRUE(it->second.outgoing_edges.front().is_controlled_return);
  EXPECT_EQ(it->second.outgoing_edges.front().restatement_kind,
            omill::EdgeRestatementKind::kControlledReturn);
}

TEST(BinaryRegionReconstructorTest,
     ReturnAddressControlledRetKeepsUnresolvedTailWhenTargetIsUnknown) {
  omill::BinaryRegionReconstructor reconstructor;
  omill::BinaryRegionReconstructionRequest request;
  request.root_target_pc = 0x401010u;
  omill::DescentReturnAddressState state;
  state.call_site_pc = 0x401000u;
  state.original_return_pc = 0x401005u;
  state.return_stack_cell_id = 11u;
  state.control_kind =
      omill::VirtualReturnAddressControlKind::kRedirectedSymbolic;
  state.suppresses_normal_fallthrough = true;
  request.initial_return_address_state = state;

  omill::FrontierCallbacks callbacks;
  callbacks.read_target_bytes = [](uint64_t pc, uint8_t *out, size_t size) {
    if (!size || pc != 0x401010u)
      return false;
    std::fill(out, out + size, 0x90);
    out[0] = 0xC3;
    return true;
  };
  callbacks.can_decode_target = [](uint64_t pc) { return pc == 0x401010u; };

  auto snapshot = reconstructor.reconstruct(request, callbacks);
  auto it = snapshot.blocks_by_pc.find(0x401010u);
  ASSERT_NE(it, snapshot.blocks_by_pc.end());
  ASSERT_EQ(it->second.outgoing_edges.size(), 1u);
  EXPECT_FALSE(it->second.outgoing_edges.front().target_pc.has_value());
  EXPECT_TRUE(it->second.outgoing_edges.front().is_controlled_return);
  EXPECT_TRUE(it->second.outgoing_edges.front().is_unresolved_indirect);
  EXPECT_EQ(it->second.outgoing_edges.front().restatement_kind,
            omill::EdgeRestatementKind::kControlledReturnUnresolved);
  EXPECT_EQ(snapshot.controlled_return_unresolved_pcs.size(), 1u);
  EXPECT_EQ(snapshot.controlled_return_unresolved_pcs.front(), 0x401010u);
}

TEST(BinaryRegionReconstructorTest,
     ExecutableResolverMarksTrustedExactFallthroughImportable) {
  omill::ExecutableContinuationResolver resolver;
  omill::ContinuationResolutionRequest request;
  request.target_pc = 0x401230u;
  request.proof = omill::ContinuationProof{};
  request.proof->raw_target_pc = 0x401230u;
  request.proof->confidence = omill::ContinuationConfidence::kTrusted;
  request.proof->liveness = omill::ContinuationLiveness::kLive;
  request.proof->resolution_kind =
      omill::ContinuationResolutionKind::kExactFallthrough;
  request.proof->import_disposition =
      omill::ContinuationImportDisposition::kRetryable;
  request.proof->is_exact_fallthrough = true;

  omill::FrontierCallbacks callbacks;
  callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };
  callbacks.is_executable_target = [](uint64_t) { return true; };

  auto result = resolver.resolve(request, callbacks);
  EXPECT_EQ(result.disposition,
            omill::ContinuationResolutionDisposition::kImportableTrustedEntry);
  EXPECT_EQ(result.updated_proof.import_disposition,
            omill::ContinuationImportDisposition::kImportable);
}

TEST(BinaryRegionReconstructorTest,
     ExecutableResolverDefersQuarantinedSelectorArmByDefault) {
  omill::ExecutableContinuationResolver resolver;
  omill::ContinuationResolutionRequest request;
  request.target_pc = 0x401230u;
  request.proof = omill::ContinuationProof{};
  request.proof->raw_target_pc = 0x401230u;
  request.proof->liveness = omill::ContinuationLiveness::kQuarantined;

  omill::FrontierCallbacks callbacks;
  callbacks.read_target_bytes = [](uint64_t, uint8_t *out, size_t size) {
    if (!size)
      return false;
    out[0] = 0xC3;
    return true;
  };

  auto result = resolver.resolve(request, callbacks);
  EXPECT_EQ(
      result.disposition,
      omill::ContinuationResolutionDisposition::kDeferredQuarantinedSelectorArm);
  EXPECT_EQ(result.updated_proof.import_disposition,
            omill::ContinuationImportDisposition::kDeferred);
}

TEST(BinaryRegionReconstructorTest,
     ExecutableResolverPromotesTerminalModeledProofFromBinaryExactFallthrough) {
  omill::ExecutableContinuationResolver resolver;
  omill::ContinuationResolutionRequest request;
  request.target_pc = 0x401230u;
  request.proof = omill::ContinuationProof{};
  request.proof->raw_target_pc = 0x401230u;
  request.proof->confidence = omill::ContinuationConfidence::kWeak;
  request.proof->liveness = omill::ContinuationLiveness::kUnknown;
  request.proof->resolution_kind =
      omill::ContinuationResolutionKind::kTerminalModeled;
  request.proof->import_disposition =
      omill::ContinuationImportDisposition::kRetryable;

  omill::FrontierCallbacks callbacks;
  callbacks.decode_target_summary = [](uint64_t pc) {
    omill::FrontierCallbacks::DecodedTargetSummary summary;
    summary.pc = pc;
    summary.next_pc = pc + 1;
    return std::optional<omill::FrontierCallbacks::DecodedTargetSummary>(
        summary);
  };
  callbacks.is_exact_call_fallthrough_target = [](uint64_t pc) {
    return pc == 0x401230u;
  };
  callbacks.is_executable_target = [](uint64_t) { return true; };

  auto result = resolver.resolve(request, callbacks);
  EXPECT_EQ(result.disposition,
            omill::ContinuationResolutionDisposition::kImportableTrustedEntry);
  EXPECT_EQ(result.updated_proof.import_disposition,
            omill::ContinuationImportDisposition::kImportable);
  EXPECT_EQ(result.updated_proof.resolution_kind,
            omill::ContinuationResolutionKind::kExactFallthrough);
  EXPECT_EQ(result.updated_proof.confidence,
            omill::ContinuationConfidence::kTrusted);
  EXPECT_TRUE(result.updated_proof.is_exact_fallthrough);
}

TEST(BinaryRegionReconstructorTest,
     BoundaryResolverClassifiesReenteringBoundaryAsModeledReentry) {
  omill::BoundaryContinuationResolver resolver;
  omill::BoundaryResolutionRequest request;
  request.target_pc = 0x401400u;
  request.boundary = omill::BoundaryFact{};
  request.boundary->boundary_pc = 0x401400u;
  request.boundary->native_target_pc = 0x401400u;
  request.boundary->continuation_pc = 0x401410u;
  request.boundary->continuation_slot_id = 7;
  request.boundary->continuation_stack_cell_id = 11;
  request.boundary->reenters_vm = true;

  auto result = resolver.resolve(request);
  EXPECT_EQ(result.disposition,
            omill::BoundaryResolutionDisposition::kModeledReentryBoundary);
  ASSERT_TRUE(result.updated_proof.has_value());
  EXPECT_EQ(result.updated_proof->resolution_kind,
            omill::ContinuationResolutionKind::kBoundaryModeled);
  EXPECT_EQ(result.updated_proof->import_disposition,
            omill::ContinuationImportDisposition::kRejected);
}

}  // namespace
