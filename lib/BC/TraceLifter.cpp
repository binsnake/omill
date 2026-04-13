/// \file TraceLifter.cpp
/// \brief Recursive trace lifter, ported from remill.
///
/// Original: third_party/remill/lib/BC/TraceLifter.cpp
/// Copyright (c) 2020 Trail of Bits, Inc.  (Apache-2.0)
///
/// Modifications for omill:
///   - Lives in namespace omill (TraceManager, TraceLifter, DevirtualizedTargetKind).
///   - Replaces glog with assert / llvm::errs().
///   - Uses explicit remill:: qualifiers for Arch, Instruction, IntrinsicTable,
///     and all utility functions.
///   - Block naming: only devirtualized targets get "block_<hex>" names to
///     avoid confusing omill passes that use extractBlockPC / collectBlockPCMap.

#include "omill/BC/TraceLifter.h"
#include "omill/BC/DecodeInstruction.h"

#include "omill/BC/LiftDatabaseProjection.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include <remill/Arch/Arch.h>
#include <remill/Arch/Instruction.h>
#include <remill/BC/ABI.h>
#include <remill/BC/InstructionLifter.h>
#include <remill/BC/IntrinsicTable.h>
#include <remill/BC/Util.h>

#include <cassert>
#include <map>
#include <set>
#include <sstream>
#include <utility>

namespace omill {

namespace {

static void annotateLiftTargetDecisionMetadata(llvm::CallInst &call,
                                               const LiftTargetDecision &decision) {
  if (auto fact = executableTargetFactFromDecision(decision))
    writeExecutableTargetFact(call, *fact);
}

using DecoderWorkList = std::set<uint64_t>;  // Ordered for determinism.
}  // namespace

// ---------------------------------------------------------------------------
// TraceManager default implementations
// ---------------------------------------------------------------------------

TraceManager::~TraceManager() {}

llvm::Function *TraceManager::GetLiftedTraceDeclaration(uint64_t) {
  return nullptr;
}

llvm::Function *TraceManager::GetLiftedTraceDefinition(uint64_t) {
  return nullptr;
}

void TraceManager::ForEachDevirtualizedTarget(
    const remill::Instruction &,
    std::function<void(uint64_t, DevirtualizedTargetKind)>) {
  // Must be extended by subclasses that have devirtualization info.
}

std::string TraceManager::TraceName(uint64_t addr) {
  std::stringstream ss;
  ss << "sub_" << std::hex << addr;
  return ss.str();
}

LiftTargetDecision TraceManager::ResolveLiftTarget(uint64_t, uint64_t raw_target_pc,
                                                   LiftTargetEdgeKind) {
  LiftTargetDecision decision;
  decision.raw_target_pc = raw_target_pc;
  decision.effective_target_pc = raw_target_pc;
  decision.classification = LiftTargetClassification::kLiftableEntry;
  decision.trust = LiftTargetTrust::kTrustedEntry;
  return decision;
}

DecodeFailureDecision TraceManager::ResolveDecodeFailure(
    uint64_t source_addr, uint64_t failed_pc, const DecodeFailureContext &) {
  DecodeFailureDecision decision;
  decision.source_pc = source_addr;
  decision.failed_pc = failed_pc;
  decision.action = DecodeFailureAction::kRedirectToTarget;
  decision.target = ResolveLiftTarget(
      source_addr, failed_pc,
      LiftTargetEdgeKind::kDecodeFailureContinuation);
  return decision;
}

// ---------------------------------------------------------------------------
// TraceLifter::Impl
// ---------------------------------------------------------------------------

class TraceLifter::Impl {
 public:
  Impl(const remill::Arch *arch_, TraceManager *manager_);

  bool Lift(uint64_t addr,
            std::function<void(uint64_t, llvm::Function *)> callback);

  void SetLiftDatabase(const LiftDatabase *db_) { lift_db = db_; }
  void SetLiftOverlayKey(std::optional<std::string> overlay_key) {
    projection_overlay_key = std::move(overlay_key);
  }

  bool ReadInstructionBytes(uint64_t addr);

  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr);
  llvm::Function *GetLiftedTraceDefinition(uint64_t addr);

  llvm::BasicBlock *GetOrCreateBlock(uint64_t block_pc) {
    auto &block = blocks[block_pc];
    if (!block) {
      // Name blocks that come from explicit control-flow targets so later
      // passes can recover their PCs. Leave the root entry block unnamed to
      // avoid treating the whole trace head like a devirtualized target.
      std::string name;
      const bool should_name =
          (devirt_targets.count(block_pc) || projected_blocks.count(block_pc)) &&
          (!active_trace_addr || block_pc != *active_trace_addr);
      const bool projected = projected_blocks.count(block_pc);
      const bool devirt = devirt_targets.count(block_pc);
      if (std::getenv("OMILL_DEBUG_TRACE_BLOCK_NAMING") != nullptr &&
          (projected || devirt)) {
        llvm::errs() << "[trace-block] pc=0x" << llvm::Twine::utohexstr(block_pc)
                     << " projected=" << (projected ? "yes" : "no")
                     << " devirt=" << (devirt ? "yes" : "no")
                     << " name=" << (should_name ? "yes" : "no") << "\n";
      }
      if (should_name) {
        std::stringstream ss;
        ss << "block_" << std::hex << block_pc;
        name = ss.str();
      }
      block = llvm::BasicBlock::Create(context, name, func);
    }
    return block;
  }

  llvm::BasicBlock *GetOrCreateMissingBlock(
      uint64_t block_pc, const LiftTargetDecision *decision = nullptr) {
    auto *bb = llvm::BasicBlock::Create(context, "", func);
    auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
    auto *mem_ptr = remill::NthArgument(func, remill::kMemoryPointerArgNum);
    llvm::IRBuilder<> ir(bb);
    auto *pc_val = llvm::ConstantInt::get(word_type, block_pc);
    auto *call = ir.CreateCall(intrinsics->missing_block->getFunctionType(),
                               intrinsics->missing_block,
                               {state_ptr, pc_val, mem_ptr});
    if (decision)
      annotateLiftTargetDecisionMetadata(*call, *decision);
    call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    ir.CreateRet(call);
    return bb;
  }

  llvm::BasicBlock *GetOrCreateTargetBlock(const LiftTargetDecision &decision) {
    if (decision.shouldLift() && decision.effective_target_pc) {
      inst_work_list.insert(*decision.effective_target_pc);
      return GetOrCreateBlock(*decision.effective_target_pc);
    }
    return GetOrCreateMissingBlock(decision.raw_target_pc, &decision);
  }

  std::optional<LiftDbProjection> ActiveProjectionForTrace(
      uint64_t trace_addr) const {
    if (!lift_db) {
      return std::nullopt;
    }

    LiftDatabaseProjector projector(*lift_db);
    if (projection_overlay_key) {
      if (const auto *overlay = lift_db->traceOverlay(*projection_overlay_key);
          overlay && overlay->function_entry_va == trace_addr) {
        if (auto projection = projector.projectOverlay(*projection_overlay_key)) {
          return projection;
        }
      }
    }
    return projector.projectFunction(trace_addr);
  }

  std::optional<uint64_t> ProjectedTargetBlock(uint64_t source_pc,
                                               uint64_t fallback_pc,
                                               LiftTargetEdgeKind edge_kind) const {
    if (!lift_db || !active_trace_addr) {
      return std::nullopt;
    }

    auto projection = ActiveProjectionForTrace(*active_trace_addr);
    if (!projection) {
      return std::nullopt;
    }

    const auto *projected_block =
        FindProjectionBlockContaining(*projection, source_pc);
    if (!projected_block) {
      return std::nullopt;
    }
    auto matches_edge = [&](const LiftDbEdgeRecord &edge) {
      switch (edge_kind) {
        case LiftTargetEdgeKind::kDirectJump:
        case LiftTargetEdgeKind::kConditionalTaken:
          return edge.kind == LiftDbEdgeKind::kBranchTaken ||
                 edge.kind == LiftDbEdgeKind::kOverlay;
        case LiftTargetEdgeKind::kConditionalNotTaken:
        case LiftTargetEdgeKind::kTraceNext:
          return edge.kind == LiftDbEdgeKind::kFallthrough ||
                 edge.kind == LiftDbEdgeKind::kOverlay;
        default:
          return false;
      }
    };

    for (const auto &edge : projected_block->successors) {
      if (edge.target_block_va == fallback_pc && matches_edge(edge)) {
        return edge.target_block_va;
      }
    }
    for (const auto &edge : projected_block->successors) {
      if (matches_edge(edge) && edge.target_block_va) {
        return edge.target_block_va;
      }
    }
    return std::nullopt;
  }

  llvm::SmallVector<uint64_t, 8> ProjectedDevirtualizedTargets(
      uint64_t source_pc) const {
    llvm::SmallVector<uint64_t, 8> targets;
    if (!lift_db || !active_trace_addr) {
      return targets;
    }

    auto projection = ActiveProjectionForTrace(*active_trace_addr);
    if (!projection) {
      return targets;
    }

    const auto *projected_block =
        FindProjectionBlockContaining(*projection, source_pc);
    if (!projected_block) {
      return targets;
    }

    for (const auto &edge : projected_block->successors) {
      if (!edge.target_block_va) {
        continue;
      }
      switch (edge.kind) {
        case LiftDbEdgeKind::kBranchTaken:
        case LiftDbEdgeKind::kOverlay:
          if (std::find(targets.begin(), targets.end(), edge.target_block_va) ==
              targets.end()) {
            targets.push_back(edge.target_block_va);
          }
          break;
        default:
          break;
      }
    }

    return targets;
  }





  llvm::BasicBlock *GetOrCreateResolvedTargetBlock(
      uint64_t source_pc, uint64_t block_pc, LiftTargetEdgeKind edge_kind) {
    if (auto projected_pc =
            ProjectedTargetBlock(source_pc, block_pc, edge_kind)) {
      block_pc = *projected_pc;
    }
    return GetOrCreateTargetBlock(
        manager.ResolveLiftTarget(source_pc, block_pc, edge_kind));
  }

  llvm::BasicBlock *GetOrCreateBranchTakenBlock(uint64_t source_pc) {
    return GetOrCreateResolvedTargetBlock(source_pc, inst.branch_taken_pc,
                                          LiftTargetEdgeKind::kConditionalTaken);
  }

  llvm::BasicBlock *GetOrCreateBranchNotTakenBlock(uint64_t source_pc) {
    assert(inst.branch_not_taken_pc != 0 &&
           "branch_not_taken_pc must be non-zero");
    return GetOrCreateResolvedTargetBlock(source_pc, inst.branch_not_taken_pc,
                                          LiftTargetEdgeKind::kConditionalNotTaken);
  }

  llvm::BasicBlock *GetOrCreateNextBlock(uint64_t source_pc) {
    return GetOrCreateResolvedTargetBlock(source_pc, inst.next_pc,
                                          LiftTargetEdgeKind::kTraceNext);
  }

  uint64_t PopTraceAddress() {
    auto trace_it = trace_work_list.begin();
    const auto trace_addr = *trace_it;
    trace_work_list.erase(trace_it);
    return trace_addr;
  }

  uint64_t PopInstructionAddress() {
    auto inst_it = inst_work_list.begin();
    const auto inst_addr = *inst_it;
    inst_work_list.erase(inst_it);
    return inst_addr;
  }

  void SeedProjectedTraceWork(uint64_t trace_addr) {
    auto projection = ActiveProjectionForTrace(trace_addr);
    if (std::getenv("OMILL_DEBUG_PROJECTED_TRACE_WORK") != nullptr) {
      llvm::errs() << "[trace-projection] root=0x"
                   << llvm::Twine::utohexstr(trace_addr)
                   << " has_projection=" << (projection ? "yes" : "no");
      if (projection) {
        llvm::errs() << " blocks=" << projection->block_order.size();
      }
      llvm::errs() << "\n";
    }
    if (!projection) {
      inst_work_list.insert(trace_addr);
      return;
    }
    if (projection->empty()) {
      inst_work_list.insert(trace_addr);
      return;
    }

    for (auto block_entry_va : projection->block_order) {
      projected_blocks.insert(block_entry_va);
      inst_work_list.insert(block_entry_va);
      (void) GetOrCreateBlock(block_entry_va);
    }

    for (auto block_entry_va : projection->block_order) {
      auto block_it = projection->blocks.find(block_entry_va);
      if (block_it == projection->blocks.end()) {
        continue;
      }
      for (const auto &edge : block_it->second.successors) {
        if (edge.kind == LiftDbEdgeKind::kCall && edge.target_block_va) {
          trace_work_list.insert(edge.target_block_va);
        }
      }
    }
  }

  const remill::Arch *const arch;
  const remill::IntrinsicTable *intrinsics;
  llvm::Type *word_type;
  llvm::LLVMContext &context;
  llvm::Module *const module;
  const uint64_t addr_mask;
  TraceManager &manager;

  llvm::Function *func;
  llvm::BasicBlock *block;
  llvm::SwitchInst *switch_inst;
  const size_t max_inst_bytes;
  std::string inst_bytes;
  remill::Instruction inst;
  remill::Instruction delayed_inst;
  DecoderWorkList trace_work_list;
  DecoderWorkList inst_work_list;
  DecoderWorkList devirt_targets;  // PCs from ForEachDevirtualizedTarget.
  DecoderWorkList projected_blocks;  // PCs seeded from LiftDatabase blocks.
  std::map<uint64_t, llvm::BasicBlock *> blocks;
  const LiftDatabase *lift_db = nullptr;
  std::optional<uint64_t> active_trace_addr;
  std::optional<std::string> projection_overlay_key;
};

TraceLifter::Impl::Impl(const remill::Arch *arch_, TraceManager *manager_)
    : arch(arch_),
      intrinsics(arch->GetInstrinsicTable()),
      word_type(arch->AddressType()),
      context(word_type->getContext()),
      module(intrinsics->async_hyper_call->getParent()),
      addr_mask(arch->address_size >= 64 ? ~0ULL
                                         : (~0ULL >> arch->address_size)),
      manager(*manager_),
      func(nullptr),
      block(nullptr),
      switch_inst(nullptr),
      max_inst_bytes(arch->MaxInstructionSize(arch->CreateInitialContext())) {
  inst_bytes.reserve(max_inst_bytes);
}

llvm::Function *TraceLifter::Impl::GetLiftedTraceDeclaration(uint64_t addr) {
  auto func = manager.GetLiftedTraceDeclaration(addr);
  if (!func || func->getParent() == module) {
    return func;
  }
  return nullptr;
}

llvm::Function *TraceLifter::Impl::GetLiftedTraceDefinition(uint64_t addr) {
  auto func = manager.GetLiftedTraceDefinition(addr);
  if (!func || func->getParent() == module) {
    return func;
  }

  assert(&(func->getContext()) == &context &&
         "GetLiftedTraceDefinition returned function from different context");

  auto func_type = llvm::dyn_cast<llvm::FunctionType>(
      remill::RecontextualizeType(func->getFunctionType(), context));

  // Handle the different-module situation by declaring the trace in this
  // module as external, with the idea that it will link to another module.
  auto extern_func = module->getFunction(func->getName());
  if (!extern_func || extern_func->getFunctionType() != func_type) {
    extern_func = llvm::Function::Create(
        func_type, llvm::GlobalValue::ExternalLinkage, func->getName(),
        module);
  } else if (extern_func->isDeclaration()) {
    extern_func->setLinkage(llvm::GlobalValue::ExternalLinkage);
  }

  return extern_func;
}

// ---------------------------------------------------------------------------
// TraceLifter public API
// ---------------------------------------------------------------------------

TraceLifter::~TraceLifter() {}

TraceLifter::TraceLifter(const remill::Arch *arch_, TraceManager &manager_)
    : TraceLifter(arch_, &manager_) {}

TraceLifter::TraceLifter(const remill::Arch *arch_, TraceManager *manager_)
    : impl(new Impl(arch_, manager_)) {}

void TraceLifter::NullCallback(uint64_t, llvm::Function *) {}

bool TraceLifter::Lift(
    uint64_t addr,
    std::function<void(uint64_t, llvm::Function *)> callback) {
  return impl->Lift(addr, callback);
}

void TraceLifter::SetLiftDatabase(const LiftDatabase *db) {
  impl->SetLiftDatabase(db);
}

void TraceLifter::SetLiftOverlayKey(std::optional<std::string> overlay_key) {
  impl->SetLiftOverlayKey(std::move(overlay_key));
}

// ---------------------------------------------------------------------------
// ReadInstructionBytes
// ---------------------------------------------------------------------------

bool TraceLifter::Impl::ReadInstructionBytes(uint64_t addr) {
  inst_bytes.clear();
  for (size_t i = 0; i < max_inst_bytes; ++i) {
    const auto byte_addr = (addr + i) & addr_mask;
    if (byte_addr < addr) {
      break;  // 32- or 64-bit address overflow.
    }
    uint8_t byte = 0;
    if (!manager.TryReadExecutableByte(byte_addr, &byte)) {
      break;
    }
    inst_bytes.push_back(static_cast<char>(byte));
  }
  return !inst_bytes.empty();
}

// ---------------------------------------------------------------------------
// Lift — the main decode/lift loop
// ---------------------------------------------------------------------------

bool TraceLifter::Impl::Lift(
    uint64_t addr,
    std::function<void(uint64_t, llvm::Function *)> callback) {

  // Reset the lifting state.
  trace_work_list.clear();
  inst_work_list.clear();
  devirt_targets.clear();
  projected_blocks.clear();
  blocks.clear();
  inst_bytes.clear();
  func = nullptr;
  switch_inst = nullptr;
  block = nullptr;
  inst.Reset();
  delayed_inst.Reset();
  active_trace_addr.reset();

  // Get a trace head that the manager knows about, or that we will
  // eventually tell the trace manager about.
  auto get_trace_decl = [this](uint64_t trace_addr) -> llvm::Function * {
    if (auto trace = GetLiftedTraceDeclaration(trace_addr)) {
      return trace;
    } else if (trace_work_list.count(trace_addr)) {
      return arch->DeclareLiftedFunction(manager.TraceName(trace_addr),
                                         module);
    } else {
      return nullptr;
    }
  };

  trace_work_list.insert(addr);
  while (!trace_work_list.empty()) {
    const auto trace_addr = PopTraceAddress();
    active_trace_addr = trace_addr;

    // Already lifted.
    func = GetLiftedTraceDefinition(trace_addr);
    if (func) {
      continue;
    }

    // Skip trace heads outside executable regions — avoids creating
    // stub functions for .rdata or other non-code addresses.
    {
      uint8_t probe;
      if (!manager.TryReadExecutableByte(trace_addr, &probe)) {
        continue;
      }
    }

    func = get_trace_decl(trace_addr);
    blocks.clear();
    devirt_targets.clear();

    if (!func || !func->isDeclaration()) {
      func = arch->DeclareLiftedFunction(manager.TraceName(trace_addr),
                                         module);
    }

    assert(func->isDeclaration() &&
           "Expected an empty function declaration for trace");

    // Fill in the function, and make sure the block with all register
    // variables jumps to the block containing the first instruction.
    arch->InitializeEmptyLiftedFunction(func);

    auto state_ptr =
        remill::NthArgument(func, remill::kStatePointerArgNum);

    if (auto entry_block = &(func->front())) {
      auto pc = remill::LoadProgramCounterArg(func);
      auto [next_pc_ref, next_pc_ref_type] =
          this->arch->DefaultLifter(*this->intrinsics)
              ->LoadRegAddress(entry_block, state_ptr,
                               remill::kNextPCVariableName);

      // Initialize NEXT_PC.
      (void) new llvm::StoreInst(pc, next_pc_ref, entry_block);

      // Branch to the first basic block.
      llvm::BranchInst::Create(GetOrCreateBlock(trace_addr), entry_block);
    }

    assert(inst_work_list.empty());
    SeedProjectedTraceWork(trace_addr);

    // Decode instructions.
    while (!inst_work_list.empty()) {
      const auto inst_addr = PopInstructionAddress();

      block = GetOrCreateBlock(inst_addr);
      switch_inst = nullptr;

      // We have already lifted this instruction block.
      if (!block->empty()) {
        continue;
      }

      // Check if this instruction corresponds to an existing trace head,
      // and if so, tail-call into that trace without decoding.
      if (inst_addr != trace_addr) {
        if (auto inst_as_trace = get_trace_decl(inst_addr)) {
          remill::AddTerminatingTailCall(block, inst_as_trace, *intrinsics);
          continue;
        }
      }

      // No executable bytes here.
      if (!ReadInstructionBytes(inst_addr)) {
        remill::AddTerminatingTailCall(block, intrinsics->missing_block,
                                       *intrinsics);
        continue;
      }

      inst.Reset();

      auto decode_ok = omill::DecodeInstruction(*arch, inst_addr, inst_bytes, inst);
      if (!decode_ok && inst_addr == trace_addr) {
        // Entry-point decode failure — the handler VA itself is invalid.
        llvm::errs() << "omill: TraceLifter: decode failed at entry 0x"
                     << llvm::Twine::utohexstr(inst_addr) << "\n";
      }
      if (!decode_ok) {
        auto failure_decision = manager.ResolveDecodeFailure(
            trace_addr, inst_addr,
            DecodeFailureContext{
                LiftTargetEdgeKind::kDecodeFailureContinuation});
        if (failure_decision.action == DecodeFailureAction::kRedirectToTarget) {
          auto *target_block = GetOrCreateTargetBlock(failure_decision.target);
          if (target_block != block) {
            llvm::BranchInst::Create(target_block, block);
          } else {
            remill::AddTerminatingTailCall(block, intrinsics->missing_block,
                                           *intrinsics);
          }
        } else if (failure_decision.action ==
                       DecodeFailureAction::kInvalidateEntry ||
                   failure_decision.action ==
                       DecodeFailureAction::kMaterializeExecutablePlaceholder) {
          llvm::BranchInst::Create(
              GetOrCreateMissingBlock(failure_decision.target.raw_target_pc,
                                      &failure_decision.target),
              block);
        } else {
          remill::AddTerminatingTailCall(block, intrinsics->missing_block,
                                         *intrinsics);
        }
        continue;
      }

      auto lift_status =
          inst.GetLifter()->LiftIntoBlock(inst, block, state_ptr);
      if (remill::kLiftedInstruction != lift_status &&
          remill::kLiftedUnsupportedInstruction != lift_status) {
        remill::AddTerminatingTailCall(block, intrinsics->error, *intrinsics);
        continue;
      }

      // For unsupported-but-decoded instructions (e.g. VERR, VERW),
      // semantics were emitted as a sync_hyper_call by the ISEL fallback.
      // The instruction's category and next_pc are still valid, so we
      // fall through to the category switch to continue the trace.

      // Handle lifting a delayed instruction.
      auto try_delay = arch->MayHaveDelaySlot(inst);
      if (try_delay) {
        delayed_inst.Reset();
        if (!ReadInstructionBytes(inst.delayed_pc) ||
            !arch->DecodeDelayedInstruction(
                inst.delayed_pc, inst_bytes, delayed_inst,
                this->arch->CreateInitialContext())) {
          llvm::errs() << "omill::TraceLifter: couldn't read delayed inst at 0x"
                       << llvm::Twine::utohexstr(inst.delayed_pc) << "\n";
          remill::AddTerminatingTailCall(block, intrinsics->error, *intrinsics);
          continue;
        }
      }

      // Functor used to add in a delayed instruction.
      auto try_add_delay_slot = [&](bool on_branch_taken_path,
                                    llvm::BasicBlock *into_block) -> void {
        if (!try_delay) {
          return;
        }
        if (!arch->NextInstructionIsDelayed(inst, delayed_inst,
                                            on_branch_taken_path)) {
          return;
        }
        lift_status = delayed_inst.GetLifter()->LiftIntoBlock(
            delayed_inst, into_block, state_ptr, true /* is_delayed */);
        if (remill::kLiftedInstruction != lift_status) {
          remill::AddTerminatingTailCall(block, intrinsics->error, *intrinsics);
        }
      };

      // Connect basic blocks based on instruction category.
      switch (inst.category) {
        case remill::Instruction::kCategoryInvalid:
        case remill::Instruction::kCategoryError:
          remill::AddTerminatingTailCall(block, intrinsics->error, *intrinsics);
          break;

        case remill::Instruction::kCategoryNormal:
        case remill::Instruction::kCategoryNoOp:
          llvm::BranchInst::Create(GetOrCreateNextBlock(inst_addr), block);
          break;

        case remill::Instruction::kCategoryDirectJump:
          try_add_delay_slot(true, block);
          llvm::BranchInst::Create(GetOrCreateResolvedTargetBlock(
                                       inst_addr, inst.branch_taken_pc,
                                       LiftTargetEdgeKind::kDirectJump),
                                   block);
          break;

        case remill::Instruction::kCategoryIndirectJump: {
          try_add_delay_slot(true, block);
          remill::AddTerminatingTailCall(block, intrinsics->jump, *intrinsics);

          auto projected_targets = ProjectedDevirtualizedTargets(inst_addr);
          if (!projected_targets.empty()) {
            for (uint64_t target : projected_targets) {
              inst_work_list.insert(target);
              devirt_targets.insert(target);
            }
          } else {
            // Ask the trace manager for devirtualized targets (e.g. from
            // binary-level jump table analysis).
            manager.ForEachDevirtualizedTarget(
                inst,
                [this](uint64_t target, DevirtualizedTargetKind) {
                  inst_work_list.insert(target);
                  devirt_targets.insert(target);
                });
          }
          break;
        }

        case remill::Instruction::kCategoryAsyncHyperCall:
          remill::AddCall(block, intrinsics->async_hyper_call, *intrinsics);
          goto check_call_return;

        case remill::Instruction::kCategoryIndirectFunctionCall: {
          try_add_delay_slot(true, block);
          const auto fall_through_block =
              llvm::BasicBlock::Create(context, "", func);

          const auto ret_pc_ref =
              remill::LoadReturnProgramCounterRef(fall_through_block);
          const auto next_pc_ref =
              remill::LoadNextProgramCounterRef(fall_through_block);
          llvm::IRBuilder<> ir(fall_through_block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);
          ir.CreateBr(
              GetOrCreateBranchNotTakenBlock(inst_addr));

          remill::AddCall(block, intrinsics->function_call, *intrinsics);
          llvm::BranchInst::Create(fall_through_block, block);
          block = fall_through_block;
          continue;
        }

        case remill::Instruction::kCategoryConditionalIndirectFunctionCall: {
          auto taken_block = llvm::BasicBlock::Create(context, "", func);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock(inst_addr);
          const auto orig_not_taken_block = not_taken_block;

          if (try_delay) {
            not_taken_block = llvm::BasicBlock::Create(context, "", func);
            try_add_delay_slot(true, taken_block);
            try_add_delay_slot(false, not_taken_block);
            llvm::BranchInst::Create(orig_not_taken_block, not_taken_block);
          }

          llvm::BranchInst::Create(taken_block, not_taken_block,
                                   remill::LoadBranchTaken(block), block);

          remill::AddCall(taken_block, intrinsics->function_call, *intrinsics);

          const auto ret_pc_ref =
              remill::LoadReturnProgramCounterRef(taken_block);
          const auto next_pc_ref =
              remill::LoadNextProgramCounterRef(taken_block);
          llvm::IRBuilder<> ir(taken_block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);
          ir.CreateBr(orig_not_taken_block);
          block = orig_not_taken_block;
          continue;
        }

        case remill::Instruction::kCategoryDirectFunctionCall: {
        direct_func_call:
          try_add_delay_slot(true, block);
          if (inst.branch_not_taken_pc != inst.branch_taken_pc) {
            auto target_decision = manager.ResolveLiftTarget(
                inst_addr, inst.branch_taken_pc,
                LiftTargetEdgeKind::kDirectCallTarget);
            if (target_decision.shouldLift() &&
                target_decision.effective_target_pc) {
              trace_work_list.insert(*target_decision.effective_target_pc);
              auto target_trace =
                  get_trace_decl(*target_decision.effective_target_pc);
              remill::AddCall(block, target_trace, *intrinsics);
            }
          }

          const auto ret_pc_ref =
              remill::LoadReturnProgramCounterRef(block);
          const auto next_pc_ref =
              remill::LoadNextProgramCounterRef(block);
          llvm::IRBuilder<> ir(block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);
          ir.CreateBr(GetOrCreateBranchNotTakenBlock(inst_addr));
          continue;
        }

        case remill::Instruction::kCategoryConditionalDirectFunctionCall: {
          if (inst.branch_not_taken_pc == inst.branch_taken_pc) {
            goto direct_func_call;
          }

          auto taken_block = llvm::BasicBlock::Create(context, "", func);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock(inst_addr);
          const auto orig_not_taken_block = not_taken_block;

          if (try_delay) {
            not_taken_block = llvm::BasicBlock::Create(context, "", func);
            try_add_delay_slot(true, taken_block);
            try_add_delay_slot(false, not_taken_block);
            llvm::BranchInst::Create(orig_not_taken_block, not_taken_block);
          }

          llvm::BranchInst::Create(taken_block, not_taken_block,
                                   remill::LoadBranchTaken(block), block);

          remill::AddCall(taken_block, intrinsics->function_call, *intrinsics);
          auto target_decision = manager.ResolveLiftTarget(
              inst_addr, inst.branch_taken_pc,
              LiftTargetEdgeKind::kDirectCallTarget);
          if (target_decision.shouldLift() &&
              target_decision.effective_target_pc) {
            trace_work_list.insert(*target_decision.effective_target_pc);
            auto target_trace =
                get_trace_decl(*target_decision.effective_target_pc);
            remill::AddCall(taken_block, target_trace, *intrinsics);
          }

          const auto ret_pc_ref =
              remill::LoadReturnProgramCounterRef(taken_block);
          const auto next_pc_ref =
              remill::LoadNextProgramCounterRef(taken_block);
          llvm::IRBuilder<> ir(taken_block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);
          ir.CreateBr(orig_not_taken_block);
          block = orig_not_taken_block;
          continue;
        }

        case remill::Instruction::kCategoryConditionalAsyncHyperCall: {
          auto do_hyper_call = llvm::BasicBlock::Create(context, "", func);
          llvm::BranchInst::Create(do_hyper_call, GetOrCreateNextBlock(inst_addr),
                                   remill::LoadBranchTaken(block), block);
          block = do_hyper_call;
          remill::AddCall(block, intrinsics->async_hyper_call, *intrinsics);
          goto check_call_return;
        }

        check_call_return:
          do {
            auto pc = remill::LoadProgramCounter(block, *intrinsics);
            auto ret_pc =
                llvm::ConstantInt::get(intrinsics->pc_type, inst.next_pc);

            llvm::IRBuilder<> ir(block);
            auto eq = ir.CreateICmpEQ(pc, ret_pc);
            auto unexpected_ret_pc =
                llvm::BasicBlock::Create(context, "", func);
            ir.CreateCondBr(eq, GetOrCreateNextBlock(inst_addr),
                            unexpected_ret_pc);
            remill::AddTerminatingTailCall(
                unexpected_ret_pc, intrinsics->missing_block, *intrinsics);
          } while (false);
          break;

        case remill::Instruction::kCategoryFunctionReturn:
          try_add_delay_slot(true, block);
          remill::AddTerminatingTailCall(block, intrinsics->function_return,
                                         *intrinsics);
          break;

        case remill::Instruction::kCategoryConditionalFunctionReturn: {
          auto taken_block = llvm::BasicBlock::Create(context, "", func);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock(inst_addr);
          const auto orig_not_taken_block = not_taken_block;

          if (try_delay) {
            not_taken_block = llvm::BasicBlock::Create(context, "", func);
            try_add_delay_slot(true, taken_block);
            try_add_delay_slot(false, not_taken_block);
            llvm::BranchInst::Create(orig_not_taken_block, not_taken_block);
          }

          llvm::BranchInst::Create(taken_block, not_taken_block,
                                   remill::LoadBranchTaken(block), block);

          remill::AddTerminatingTailCall(taken_block,
                                         intrinsics->function_return,
                                         *intrinsics);
          block = orig_not_taken_block;
          continue;
        }

        case remill::Instruction::kCategoryConditionalBranch: {
          auto taken_block = GetOrCreateBranchTakenBlock(inst_addr);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock(inst_addr);

          if (try_delay) {
            auto new_taken_block =
                llvm::BasicBlock::Create(context, "", func);
            auto new_not_taken_block =
                llvm::BasicBlock::Create(context, "", func);

            try_add_delay_slot(true, new_taken_block);
            try_add_delay_slot(false, new_not_taken_block);

            llvm::BranchInst::Create(taken_block, new_taken_block);
            llvm::BranchInst::Create(not_taken_block, new_not_taken_block);

            taken_block = new_taken_block;
            not_taken_block = new_not_taken_block;
          }

          llvm::BranchInst::Create(taken_block, not_taken_block,
                                   remill::LoadBranchTaken(block), block);
          break;
        }

        case remill::Instruction::kCategoryConditionalIndirectJump: {
          auto taken_block = llvm::BasicBlock::Create(context, "", func);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock(inst_addr);
          const auto orig_not_taken_block = not_taken_block;

          if (try_delay) {
            not_taken_block = llvm::BasicBlock::Create(context, "", func);
            try_add_delay_slot(true, taken_block);
            try_add_delay_slot(false, not_taken_block);
            llvm::BranchInst::Create(orig_not_taken_block, not_taken_block);
          }

          llvm::BranchInst::Create(taken_block, not_taken_block,
                                   remill::LoadBranchTaken(block), block);

          remill::AddTerminatingTailCall(taken_block, intrinsics->jump,
                                         *intrinsics);
          block = orig_not_taken_block;
          continue;
        }
      }
    }

    for (auto &block : *func) {
      if (!block.getTerminator()) {
        remill::AddTerminatingTailCall(&block, intrinsics->missing_block,
                                       *intrinsics);
      }
    }

    callback(trace_addr, func);
    manager.SetLiftedTraceDefinition(trace_addr, func);
  }

  active_trace_addr.reset();

  return true;
}

}  // namespace omill
