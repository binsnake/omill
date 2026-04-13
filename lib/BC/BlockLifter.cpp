/// \file BlockLifter.cpp
/// \brief Per-basic-block lifter for iterative target resolution.
///
/// See include/omill/BC/BlockLifter.h for design rationale.

#include "omill/BC/BlockLifter.h"
#include "omill/BC/DecodeInstruction.h"

#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/BC/LiftDatabase.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Utils/LiftedNames.h"

#include <llvm/ADT/DenseMap.h>

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

#include <algorithm>
#include <cassert>
#include <cstring>
#include <queue>
#include <set>
#include <sstream>

#include "omill/BC/LiftDatabaseProjection.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {
namespace {

template <typename T>
static void PushUnique(std::vector<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

template <typename T>
static void PushUnique(llvm::SmallVectorImpl<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

}  // namespace

// ---------------------------------------------------------------------------
// BlockManager default implementations
// ---------------------------------------------------------------------------

BlockManager::~BlockManager() {}

std::string BlockManager::BlockName(uint64_t addr) {
  std::stringstream ss;
  ss << (IsFunctionEntry(addr) ? "sub_" : "blk_") << std::hex << addr;
  return ss.str();
}

void BlockManager::MarkFunctionEntry(uint64_t addr) {
  function_entry_pcs_.insert(addr);
}

bool BlockManager::IsFunctionEntry(uint64_t addr) const {
  return function_entry_pcs_.count(addr) != 0;
}

llvm::Function *BlockManager::GetLiftedBlockDeclaration(uint64_t) {
  return nullptr;
}

llvm::Function *BlockManager::GetLiftedBlockDefinition(uint64_t) {
  return nullptr;
}

llvm::Module *BlockManager::GetLiftedBlockModule() {
  return nullptr;
}

static void annotateLiftTargetDecisionMetadata(llvm::CallInst &call,
                                               const LiftTargetDecision &decision);

LiftTargetDecision BlockManager::ResolveLiftTarget(uint64_t, uint64_t raw_target_pc,
                                                   LiftTargetEdgeKind) {
  LiftTargetDecision decision;
  decision.raw_target_pc = raw_target_pc;
  decision.effective_target_pc = raw_target_pc;
  decision.classification = LiftTargetClassification::kLiftableEntry;
  decision.trust = LiftTargetTrust::kTrustedEntry;
  return decision;
}

DecodeFailureDecision BlockManager::ResolveDecodeFailure(
    uint64_t source_addr, uint64_t failed_pc, const DecodeFailureContext &) {
  DecodeFailureDecision decision;
  decision.source_pc = source_addr;
  decision.failed_pc = failed_pc;
  decision.action = DecodeFailureAction::kRedirectToTarget;
  decision.target = ResolveLiftTarget(
      source_addr, failed_pc, LiftTargetEdgeKind::kDecodeFailureContinuation);
  return decision;
}

void BlockManager::ForEachDevirtualizedTarget(
    const remill::Instruction &,
    std::function<void(uint64_t, DevirtualizedTargetKind)>) {
  // No-op: subclasses override to provide jump table targets.
}

// ---------------------------------------------------------------------------
// BlockLifter::Impl
// ---------------------------------------------------------------------------

class BlockLifter::Impl {
 public:
  Impl(const remill::Arch *arch_, BlockManager &manager_);

  llvm::Function *LiftBlock(
      uint64_t addr,
      llvm::SmallVectorImpl<uint64_t> &discovered_targets);

  unsigned LiftReachable(uint64_t addr);
  void SetLiftDatabase(const LiftDatabase *db_) { lift_db = db_; }

  llvm::Module *GetModule() const { return module; }

 private:
  bool ReadInstructionBytes(uint64_t addr);

  /// Declare a block-function (empty declaration with lifted signature).
  llvm::Function *DeclareBlockFunction(uint64_t addr);

  /// Get existing declaration or create one.
  llvm::Function *GetOrDeclareBlockFunction(uint64_t addr);

  /// Mark \p addr as a function entry (so it is named `sub_<pc>`) and
  /// rename any previously-declared `blk_<pc>` stub to match.
  void MarkFunctionEntryAndUpgradeName(uint64_t addr);

  /// Emit a musttail call to a block-function and ret.
  /// This is the standard inter-block transfer for direct jumps/branches.
  void EmitMusttailToBlock(llvm::BasicBlock *from_bb,
                           llvm::Function *target_fn,
                           uint64_t target_pc);

  /// Emit a musttail call to the missing-block intrinsic with a specific PC.
  llvm::CallInst *EmitMusttailToMissingBlock(llvm::BasicBlock *from_bb,
                                             uint64_t target_pc,
                                             const LiftTargetDecision *decision =
                                                 nullptr);

  /// Emit a call to the configured unresolved jump dispatcher.
  void EmitDispatchJump(llvm::BasicBlock *bb);

  /// Emit a call to the configured unresolved call dispatcher + musttail to
  /// the fall-through block.
  void EmitDispatchCallAndFallthrough(llvm::BasicBlock *bb,
                                      uint64_t fallthrough_pc,
                                      const LiftTargetDecision &fallthrough_decision,
                                      llvm::SmallVectorImpl<uint64_t> &targets);

  void EmitDecisionEdge(llvm::BasicBlock *from_bb, uint64_t raw_target_pc,
                        const LiftTargetDecision &decision,
                        llvm::SmallVectorImpl<uint64_t> &discovered_targets);

  void EmitDecisionEdgeWithMemory(
      llvm::BasicBlock *from_bb, uint64_t raw_target_pc,
      const LiftTargetDecision &decision, llvm::Value *memory_value,
      llvm::SmallVectorImpl<uint64_t> &discovered_targets);

  bool PopulateProjectedTargets(
      uint64_t addr, llvm::SmallVectorImpl<uint64_t> &discovered_targets) const;

  const remill::Arch *const arch;
  const remill::IntrinsicTable *intrinsics;
  llvm::Type *word_type;
  llvm::LLVMContext &context;
  llvm::Module *const module;
  const uint64_t addr_mask;
  BlockManager &manager;

  const size_t max_inst_bytes;
  std::string inst_bytes;
  remill::Instruction inst;
  remill::Instruction delayed_inst;
  const LiftDatabase *lift_db = nullptr;

  /// Cached results of analyzeCallTargetBridgeEffect keyed by call-target
  /// PC.  Populated lazily when lift_db has no descriptor for a direct
  /// call.  Entries may be std::nullopt to indicate a previously-rejected
  /// target that should not be re-analyzed.
  llvm::DenseMap<uint64_t, std::optional<CallTargetBridgeEffect>>
      bridge_cache;

  /// Try to obtain a call-target bridge descriptor for a direct-call
  /// target.  Prefers the lift-db record; falls back to an in-process run
  /// of the analyzer using the BlockManager's BinaryMemoryMap when
  /// available.
  std::optional<CallTargetBridgeEffect> LookupBridgeEffect(
      uint64_t call_instruction_pc, uint64_t call_target_pc);
};

BlockLifter::Impl::Impl(const remill::Arch *arch_, BlockManager &manager_)
    : arch(arch_),
      intrinsics(arch->GetInstrinsicTable()),
      word_type(arch->AddressType()),
      context(word_type->getContext()),
      module(manager_.GetLiftedBlockModule()
                 ? manager_.GetLiftedBlockModule()
                 : intrinsics->async_hyper_call->getParent()),
      addr_mask(arch->address_size >= 64 ? ~0ULL
                                         : (~0ULL >> arch->address_size)),
      manager(manager_),
      max_inst_bytes(arch->MaxInstructionSize(arch->CreateInitialContext())) {
  inst_bytes.reserve(max_inst_bytes);
}

bool BlockLifter::Impl::PopulateProjectedTargets(
    uint64_t addr, llvm::SmallVectorImpl<uint64_t> &discovered_targets) const {
  if (!lift_db) {
    return false;
  }

  LiftDatabaseProjector projector(*lift_db);
  auto projection = projector.projectBlock(addr);
  if (!projection) {
    return false;
  }

  auto block_it = projection->blocks.find(addr);
  if (block_it == projection->blocks.end()) {
    return false;
  }

  discovered_targets.clear();
  for (const auto &edge : block_it->second.successors) {
    if (!edge.target_block_va) {
      continue;
    }
    switch (edge.kind) {
      case LiftDbEdgeKind::kFallthrough:
      case LiftDbEdgeKind::kBranchTaken:
      case LiftDbEdgeKind::kOverlay:
        PushUnique(discovered_targets, edge.target_block_va);
        break;
      default:
        break;
    }
  }

  return true;
}

// ---------------------------------------------------------------------------
// Call-target bridge lookup
// ---------------------------------------------------------------------------

std::optional<CallTargetBridgeEffect> BlockLifter::Impl::LookupBridgeEffect(
    uint64_t call_instruction_pc, uint64_t call_target_pc) {
  if (!call_target_pc) {
    return std::nullopt;
  }

  // Prefer the persistent descriptor on the lift-db instruction record.
  if (lift_db) {
    if (const auto *rec = lift_db->instruction(call_instruction_pc);
        rec && rec->call_target_bridge.has_value()) {
      const auto &bridge = *rec->call_target_bridge;
      CallTargetBridgeEffect effect;
      effect.stack_writes.reserve(bridge.stack_writes.size());
      for (const auto &w : bridge.stack_writes) {
        BridgeStackWrite e;
        e.rsp_offset = w.rsp_offset;
        e.size_bytes = w.size_bytes;
        e.value = w.value;
        effect.stack_writes.push_back(e);
      }
      effect.net_rsp_delta = bridge.net_rsp_delta;
      effect.final_jump_target_pc = bridge.final_jump_target_pc;
      effect.terminator =
          static_cast<CallTargetBridgeEffect::Terminator>(bridge.terminator);
      effect.instructions_modeled = bridge.instructions_modeled;
      return effect;
    }
  }

  // In-process fallback: use the BlockManager's BinaryMemoryMap.
  const auto *memory_map = manager.GetBinaryMemoryMap();
  if (!memory_map) {
    return std::nullopt;
  }

  auto it = bridge_cache.find(call_target_pc);
  if (it != bridge_cache.end()) {
    return it->second;
  }
  auto effect = analyzeCallTargetBridgeEffect(*memory_map, call_target_pc);
  bridge_cache[call_target_pc] = effect;
  return effect;
}

// ---------------------------------------------------------------------------
// Instruction bytes
// ---------------------------------------------------------------------------

bool BlockLifter::Impl::ReadInstructionBytes(uint64_t addr) {
  inst_bytes.clear();
  for (size_t i = 0; i < max_inst_bytes; ++i) {
    const auto byte_addr = (addr + i) & addr_mask;
    if (byte_addr < addr) {
      break;
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
// Block-function creation helpers
// ---------------------------------------------------------------------------

llvm::Function *BlockLifter::Impl::DeclareBlockFunction(uint64_t addr) {
  auto name = manager.BlockName(addr);
  return arch->DeclareLiftedFunction(name, module);
}

llvm::Function *BlockLifter::Impl::GetOrDeclareBlockFunction(uint64_t addr) {
  auto name = manager.BlockName(addr);
  if (auto *fn = module->getFunction(name)) {
    return fn;
  }
  // Fall back: if this PC is now a function entry (sub_<pc>) but was
  // earlier declared as a plain block (blk_<pc>), rename the existing
  // declaration so every call site and cache entry continues to point
  // at the same llvm::Function.
  if (manager.IsFunctionEntry(addr)) {
    std::stringstream legacy;
    legacy << "blk_" << std::hex << addr;
    if (auto *existing = module->getFunction(legacy.str())) {
      existing->setName(name);
      return existing;
    }
  }
  return DeclareBlockFunction(addr);
}

void BlockLifter::Impl::MarkFunctionEntryAndUpgradeName(uint64_t addr) {
  const bool was_entry = manager.IsFunctionEntry(addr);
  manager.MarkFunctionEntry(addr);
  if (was_entry) {
    return;
  }
  // If the PC was previously declared as a blk_<pc>, rename it so the
  // function carries its canonical sub_<pc> name going forward.
  std::stringstream legacy;
  legacy << "blk_" << std::hex << addr;
  if (auto *existing = module->getFunction(legacy.str())) {
    existing->setName(manager.BlockName(addr));
  }
}

// ---------------------------------------------------------------------------
// Memory token helper
// ---------------------------------------------------------------------------

/// Load the current memory token from the MEMORY alloca if it exists,
/// otherwise fall back to the raw memory function argument.  Decode-failure
/// stub blocks have no MEMORY alloca, so the fallback is necessary.
static llvm::Value *LoadCurrentMemoryToken(
    llvm::IRBuilder<> &ir, llvm::Function *func,
    const remill::IntrinsicTable &intrinsics) {
  auto [mem_ref, _] = remill::FindVarInFunction(func, "MEMORY", true);
  if (mem_ref)
    return ir.CreateLoad(intrinsics.mem_ptr_type, mem_ref);
  return remill::NthArgument(func, remill::kMemoryPointerArgNum);
}

// ---------------------------------------------------------------------------
// Terminator emission
// ---------------------------------------------------------------------------

void BlockLifter::Impl::EmitMusttailToBlock(llvm::BasicBlock *from_bb,
                                            llvm::Function *target_fn,
                                            uint64_t target_pc) {
  auto *func = from_bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);

  llvm::IRBuilder<> ir(from_bb);
  auto *mem_ptr = LoadCurrentMemoryToken(ir, func, *intrinsics);
  auto *pc_val = llvm::ConstantInt::get(word_type, target_pc);
  auto *call = ir.CreateCall(target_fn->getFunctionType(), target_fn,
                             {state_ptr, pc_val, mem_ptr});
  call->setTailCallKind(llvm::CallInst::TCK_MustTail);
  ir.CreateRet(call);
}

llvm::CallInst *BlockLifter::Impl::EmitMusttailToMissingBlock(
    llvm::BasicBlock *from_bb, uint64_t target_pc,
    const LiftTargetDecision *decision) {
  auto *func = from_bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);

  llvm::IRBuilder<> ir(from_bb);
  auto *mem_ptr = LoadCurrentMemoryToken(ir, func, *intrinsics);
  auto *pc_val = llvm::ConstantInt::get(word_type, target_pc);
  auto *call = ir.CreateCall(intrinsics->missing_block->getFunctionType(),
                             intrinsics->missing_block,
                             {state_ptr, pc_val, mem_ptr});
  if (decision)
    annotateLiftTargetDecisionMetadata(*call, *decision);
  call->setTailCallKind(llvm::CallInst::TCK_MustTail);
  ir.CreateRet(call);
  return call;
}

static void ClearBasicBlockInstructions(llvm::BasicBlock *bb) {
  while (!bb->empty()) {
    bb->back().dropAllReferences();
    bb->back().eraseFromParent();
  }
}

static void annotateLiftTargetDecisionMetadata(llvm::CallInst &call,
                                               const LiftTargetDecision &decision) {
  if (auto fact = executableTargetFactFromDecision(decision))
    writeExecutableTargetFact(call, *fact);
}

void BlockLifter::Impl::EmitDispatchJump(llvm::BasicBlock *bb) {
  auto *func = bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);

  // Load the target PC.  For indirect jumps, the JMP semantic template
  // writes the target to REG_PC (State+2472) inside an opaque call.
  // Create a fresh load from State.PC at the current insertion point
  // (after the semantic call) — GVN will forward the template's store
  // to this load after the template is inlined by AlwaysInlinerPass.
  auto *next_pc = remill::LoadProgramCounter(bb, *intrinsics);

  // Get or create the configured unresolved jump dispatcher.
  auto *lifted_fn_ty = func->getFunctionType();
  auto dispatch = module->getOrInsertFunction(
      canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kJump, *module),
      lifted_fn_ty);

  llvm::IRBuilder<> ir(bb);
  auto *mem_ptr = LoadCurrentMemoryToken(ir, func, *intrinsics);
  auto *result = ir.CreateCall(dispatch, {state_ptr, next_pc, mem_ptr});
  ir.CreateRet(result);
}

void BlockLifter::Impl::EmitDispatchCallAndFallthrough(
    llvm::BasicBlock *bb,
    uint64_t fallthrough_pc,
    const LiftTargetDecision &fallthrough_decision,
    llvm::SmallVectorImpl<uint64_t> &targets) {
  auto *func = bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);

  // Load the target PC for the call.
  auto *call_pc = remill::LoadNextProgramCounter(bb, *intrinsics);

  // Get or create the configured unresolved call dispatcher.
  auto *lifted_fn_ty = func->getFunctionType();
  auto dispatch = module->getOrInsertFunction(
      canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kCall, *module),
      lifted_fn_ty);

  llvm::IRBuilder<> ir(bb);
  auto *mem_ptr = LoadCurrentMemoryToken(ir, func, *intrinsics);
  auto *call_result = ir.CreateCall(dispatch, {state_ptr, call_pc, mem_ptr});

  // The call returns Memory*.  Now musttail to the fall-through block.
  EmitDecisionEdgeWithMemory(bb, fallthrough_pc, fallthrough_decision,
                             call_result, targets);
}

void BlockLifter::Impl::EmitDecisionEdge(
    llvm::BasicBlock *from_bb, uint64_t raw_target_pc,
    const LiftTargetDecision &decision,
    llvm::SmallVectorImpl<uint64_t> &discovered_targets) {
  if (decision.shouldLift() && decision.effective_target_pc) {
    discovered_targets.push_back(*decision.effective_target_pc);
    auto *target_fn = GetOrDeclareBlockFunction(*decision.effective_target_pc);
    EmitMusttailToBlock(from_bb, target_fn, *decision.effective_target_pc);
    return;
  }
  EmitMusttailToMissingBlock(from_bb, raw_target_pc, &decision);
}

void BlockLifter::Impl::EmitDecisionEdgeWithMemory(
    llvm::BasicBlock *from_bb, uint64_t raw_target_pc,
    const LiftTargetDecision &decision, llvm::Value *memory_value,
    llvm::SmallVectorImpl<uint64_t> &discovered_targets) {
  if (decision.shouldLift() && decision.effective_target_pc) {
    auto *func = from_bb->getParent();
    auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
    llvm::IRBuilder<> ir(from_bb);
    discovered_targets.push_back(*decision.effective_target_pc);
    auto *target_fn = GetOrDeclareBlockFunction(*decision.effective_target_pc);
    auto *ft_pc =
        llvm::ConstantInt::get(word_type, *decision.effective_target_pc);
    auto *ft_call = ir.CreateCall(target_fn->getFunctionType(), target_fn,
                                  {state_ptr, ft_pc, memory_value});
    ft_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    ir.CreateRet(ft_call);
    return;
  }

  auto *func = from_bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
  llvm::IRBuilder<> ir(from_bb);
  auto *pc_val = llvm::ConstantInt::get(word_type, raw_target_pc);
  auto *call = ir.CreateCall(intrinsics->missing_block->getFunctionType(),
                             intrinsics->missing_block,
                             {state_ptr, pc_val, memory_value});
  annotateLiftTargetDecisionMetadata(*call, decision);
  call->setTailCallKind(llvm::CallInst::TCK_MustTail);
  ir.CreateRet(call);
}

// ---------------------------------------------------------------------------
// LiftBlock — core per-block lifting
// ---------------------------------------------------------------------------

llvm::Function *BlockLifter::Impl::LiftBlock(
    uint64_t addr,
    llvm::SmallVectorImpl<uint64_t> &discovered_targets) {

  // Already lifted?
  auto name = manager.BlockName(addr);
  if (auto *existing = module->getFunction(name);
      existing && !existing->isDeclaration()) {
    PopulateProjectedTargets(addr, discovered_targets);
    return existing;
  }

  // Get or create declaration, then define it.
  auto *func = GetOrDeclareBlockFunction(addr);
  if (!func->isDeclaration()) {
    // Someone already defined it (shouldn't happen, but be safe).
    return func;
  }

  // Initialize the function with remill's standard entry setup:
  // BRANCH_TAKEN, RETURN_PC, MONITOR allocas.
  arch->InitializeEmptyLiftedFunction(func);

  // Mark the function as a BlockLifter output so MergeBlockFunctionsPass
  // can safely distinguish block-lifter entries (both `sub_<pc>` and
  // `blk_<pc>`) from TraceLifter-produced `sub_<pc>` functions.
  func->addFnAttr("omill.block_lifter");

  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
  auto *entry_block = &func->front();

  // Store NEXT_PC = pc argument in the entry block.
  {
    auto pc = remill::LoadProgramCounterArg(func);
    auto [next_pc_ref, next_pc_ref_type] =
        arch->DefaultLifter(*intrinsics)
            ->LoadRegAddress(entry_block, state_ptr,
                             remill::kNextPCVariableName);
    (void) new llvm::StoreInst(pc, next_pc_ref, entry_block);
  }

  // Create body block and branch entry → body.
  auto *body = llvm::BasicBlock::Create(context, "body", func);
  llvm::BranchInst::Create(body, entry_block);

  // Decode instructions within this basic block.
  auto *current_block = body;
  uint64_t current_pc = addr;
  bool lift_crashed = false;
  bool invalidated_block_entry = false;
  std::optional<LiftTargetDecision> invalidated_block_decision;
  __try {
    while (true) {
    // No executable bytes?
    if (!ReadInstructionBytes(current_pc)) {
      remill::AddTerminatingTailCall(current_block, intrinsics->missing_block,
                                     *intrinsics);
      break;
    }

    inst.Reset();
    auto decode_ok = omill::DecodeInstruction(*arch, current_pc, inst_bytes, inst);
    if (!decode_ok) {
      llvm::errs() << "omill: BlockLifter: decode failed at 0x"
                   << llvm::Twine::utohexstr(current_pc) << "\n";
      auto failure_decision = manager.ResolveDecodeFailure(
          addr, current_pc,
            DecodeFailureContext{
                LiftTargetEdgeKind::kDecodeFailureContinuation});
      if (failure_decision.action == DecodeFailureAction::kInvalidateEntry) {
        discovered_targets.clear();
        for (auto it = func->begin(), end = func->end(); it != end; ++it) {
          ClearBasicBlockInstructions(&*it);
        }
        invalidated_block_entry = true;
        invalidated_block_decision = failure_decision.target;
        current_block = &func->getEntryBlock();
        EmitMusttailToMissingBlock(current_block, addr,
                                   &failure_decision.target);
        break;
      }
      if (failure_decision.action == DecodeFailureAction::kRedirectToTarget &&
          failure_decision.target.effective_target_pc &&
          *failure_decision.target.effective_target_pc != addr) {
        EmitDecisionEdge(current_block, current_pc, failure_decision.target,
                         discovered_targets);
      } else if (failure_decision.action ==
                 DecodeFailureAction::kMaterializeExecutablePlaceholder) {
        EmitMusttailToMissingBlock(current_block, current_pc,
                                   &failure_decision.target);
      } else {
        remill::AddTerminatingTailCall(current_block, intrinsics->missing_block,
                                       *intrinsics);
      }
      break;
    }

    auto lift_status =
        inst.GetLifter()->LiftIntoBlock(inst, current_block, state_ptr);
    if (remill::kLiftedInstruction != lift_status) {
      // Remill has no ISEL for some control-flow categories that XED still
      // decodes successfully — most notably FAR call (CALL_FAR_MEMp2 and
      // CALL_FAR_PTRp_IMMw, see remill/lib/Arch/X86/Semantics/CALL_RET.cpp).
      // Those instructions are categorized as kCategoryAsyncHyperCall, and
      // the corresponding category handler below just emits
      // intrinsics->async_hyper_call without depending on any
      // semantic-side-effects of LiftIntoBlock. Letting the category switch
      // run produces a clean trap (lowerAsyncHyperCall's default arm emits
      // `ud2`) instead of leaking an __omill_error_handler call.
      if (inst.category != remill::Instruction::kCategoryAsyncHyperCall) {
        remill::AddTerminatingTailCall(current_block, intrinsics->error,
                                       *intrinsics);
        break;
      }
      // Fall through to the category switch with whatever partial NEXT_PC
      // state remill set up; the AsyncHyperCall handler ignores it.
    }

    // Handle delayed instructions (SPARC, MIPS).
    auto try_delay = arch->MayHaveDelaySlot(inst);
    if (try_delay) {
      delayed_inst.Reset();
      if (!ReadInstructionBytes(inst.delayed_pc) ||
          !arch->DecodeDelayedInstruction(inst.delayed_pc, inst_bytes,
                                          delayed_inst,
                                          arch->CreateInitialContext())) {
        llvm::errs()
            << "omill::BlockLifter: couldn't read delayed inst at 0x"
            << llvm::Twine::utohexstr(inst.delayed_pc) << "\n";
        remill::AddTerminatingTailCall(current_block, intrinsics->error,
                                       *intrinsics);
        break;
      }
    }

    auto try_add_delay_slot = [&](bool on_branch_taken_path,
                                  llvm::BasicBlock *into_block) {
      if (!try_delay) return;
      if (!arch->NextInstructionIsDelayed(inst, delayed_inst,
                                          on_branch_taken_path)) {
        return;
      }
      auto ds_status = delayed_inst.GetLifter()->LiftIntoBlock(
          delayed_inst, into_block, state_ptr, true);
      if (remill::kLiftedInstruction != ds_status) {
        remill::AddTerminatingTailCall(into_block, intrinsics->error,
                                       *intrinsics);
      }
    };

    // ---------------------------------------------------------------
    // Category switch — analogous to TraceLifter, but inter-block
    // transitions become musttail calls to block-functions.
    // ---------------------------------------------------------------
    switch (inst.category) {
      case remill::Instruction::kCategoryInvalid:
      case remill::Instruction::kCategoryError:
        remill::AddTerminatingTailCall(current_block, intrinsics->error,
                                       *intrinsics);
        goto done;  // End of block.

      case remill::Instruction::kCategoryNormal:
      case remill::Instruction::kCategoryNoOp:
        // Continue decoding the next instruction in this block.
        current_pc = inst.next_pc;
        continue;

      case remill::Instruction::kCategoryDirectJump: {
        try_add_delay_slot(true, current_block);
        auto target = inst.branch_taken_pc;
        auto target_decision = manager.ResolveLiftTarget(
            current_pc, target, LiftTargetEdgeKind::kDirectJump);
        EmitDecisionEdge(current_block, target, target_decision,
                         discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryIndirectJump: {
        try_add_delay_slot(true, current_block);
        // The JMP semantic was already lifted (line 638).  It calls
        // __remill_jump(state, target, memory) internally, which
        // sets PC = target.  Don't call EmitDispatchJump — the
        // template call is opaque and PC/NEXT_PC hold stale values.
        // Instead, terminate with the __remill_jump that the
        // semantic template emits (visible after AlwaysInliner).
        // Phase 3 LowerRemillIntrinsics will convert it to
        // dispatch_jump with the correct target.
        {
          llvm::IRBuilder<> ir(current_block);
          auto *mem = LoadCurrentMemoryToken(ir, func, *intrinsics);
          ir.CreateRet(mem);
        }

        llvm::SmallVector<uint64_t, 8> projected_targets;
        if (PopulateProjectedTargets(addr, projected_targets) &&
            !projected_targets.empty()) {
          for (uint64_t target : projected_targets) {
            PushUnique(discovered_targets, target);
          }
        } else {
          // Ask the manager for devirtualized targets.
          manager.ForEachDevirtualizedTarget(
              inst,
              [&](uint64_t target, DevirtualizedTargetKind) {
                auto decision = manager.ResolveLiftTarget(
                    current_pc, target, LiftTargetEdgeKind::kIndirectTarget);
                if (decision.shouldLift() && decision.effective_target_pc) {
                  PushUnique(discovered_targets, *decision.effective_target_pc);
                } else if (decision.effective_target_pc) {
                  PushUnique(discovered_targets, *decision.effective_target_pc);
                } else if (decision.raw_target_pc) {
                  PushUnique(discovered_targets, decision.raw_target_pc);
                }
              });
        }
        goto done;
      }

      case remill::Instruction::kCategoryConditionalBranch: {
        auto taken_pc = inst.branch_taken_pc;
        auto not_taken_pc = inst.branch_not_taken_pc;
        auto taken_target = manager.ResolveLiftTarget(
            current_pc, taken_pc, LiftTargetEdgeKind::kConditionalTaken);
        auto not_taken_target = manager.ResolveLiftTarget(
            current_pc, not_taken_pc, LiftTargetEdgeKind::kConditionalNotTaken);

        auto *taken_bb = llvm::BasicBlock::Create(context, "taken", func);
        auto *not_taken_bb =
            llvm::BasicBlock::Create(context, "not_taken", func);

        if (try_delay) {
          auto *ds_taken = llvm::BasicBlock::Create(context, "ds_taken", func);
          auto *ds_not_taken =
              llvm::BasicBlock::Create(context, "ds_not_taken", func);

          try_add_delay_slot(true, ds_taken);
          try_add_delay_slot(false, ds_not_taken);

          // ds blocks → actual exit blocks.
          if (!ds_taken->getTerminator()) {
            llvm::BranchInst::Create(taken_bb, ds_taken);
          }
          if (!ds_not_taken->getTerminator()) {
            llvm::BranchInst::Create(not_taken_bb, ds_not_taken);
          }

          llvm::BranchInst::Create(ds_taken, ds_not_taken,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        } else {
          llvm::BranchInst::Create(taken_bb, not_taken_bb,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        }

        EmitDecisionEdge(taken_bb, taken_pc, taken_target, discovered_targets);
        EmitDecisionEdge(not_taken_bb, not_taken_pc, not_taken_target,
                         discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryDirectFunctionCall: {
        try_add_delay_slot(true, current_block);
        auto call_target = inst.branch_taken_pc;
        auto fallthrough = inst.branch_not_taken_pc;
        auto fallthrough_target = manager.ResolveLiftTarget(
            current_pc, fallthrough, LiftTargetEdgeKind::kCallFallthrough);
        auto call_target_decision = manager.ResolveLiftTarget(
            current_pc, call_target, LiftTargetEdgeKind::kDirectCallTarget);

        // Direct call targets are canonical function entries — name them
        // `sub_<pc>` up front so downstream inlining / ABI recovery /
        // calling-convention passes recognize them without waiting for
        // MergeBlockFunctionsPass to rename.
        if (const uint64_t entry_pc =
                call_target_decision.effective_target_pc
                    ? *call_target_decision.effective_target_pc
                    : call_target;
            entry_pc != 0) {
          MarkFunctionEntryAndUpgradeName(entry_pc);
        }

        // Generic call-target bridge path.  StaticLiftBuilder (or the
        // in-process fallback analyzer) probe-decodes the target's
        // prologue; if it turns out to be a deterministic stack-effect
        // thunk (VMProtect-style return-address manipulation and
        // similar), we replay the stack writes inline at the call site
        // so no `omill_native_boundary_<thunk_pc>` placeholder ever
        // needs to exist.  Any written constants stay on the simulated
        // stack and will be consumed by a later lifted `ret`; the
        // caller then resumes at its own fallthrough as if the call had
        // returned immediately.
        if (auto bridge = LookupBridgeEffect(current_pc, call_target);
            bridge && bridge->terminator ==
                          CallTargetBridgeEffect::Terminator::kJmpConst) {
          auto [rsp_addr, rsp_type] =
              arch->DefaultLifter(*intrinsics)
                  ->LoadRegAddress(current_block, state_ptr, "RSP");

          llvm::IRBuilder<> ir(current_block);
          auto *entry_rsp =
              ir.CreateLoad(word_type, rsp_addr, "rsp.entry");

          for (const auto &write : bridge->stack_writes) {
            auto *offset_val = llvm::ConstantInt::get(
                word_type, static_cast<uint64_t>(write.rsp_offset),
                /*isSigned=*/true);
            auto *slot_rsp = ir.CreateAdd(entry_rsp, offset_val,
                                           "rsp.bridge.slot");
            auto *slot_ptr = ir.CreateIntToPtr(
                slot_rsp, llvm::PointerType::getUnqual(context),
                "rsp.bridge.ptr");
            llvm::Type *store_ty = nullptr;
            switch (write.size_bytes) {
              case 1:
                store_ty = llvm::Type::getInt8Ty(context);
                break;
              case 2:
                store_ty = llvm::Type::getInt16Ty(context);
                break;
              case 4:
                store_ty = llvm::Type::getInt32Ty(context);
                break;
              case 8:
              default:
                store_ty = word_type;
                break;
            }
            auto *stored = llvm::ConstantInt::get(
                store_ty, write.value, /*isSigned=*/false);
            ir.CreateStore(stored, slot_ptr);
          }

          auto *new_rsp = ir.CreateAdd(
              entry_rsp,
              llvm::ConstantInt::get(
                  word_type, static_cast<uint64_t>(bridge->net_rsp_delta),
                  /*isSigned=*/true),
              "rsp.bridge.new");
          ir.CreateStore(new_rsp, rsp_addr);

          // Emit register writes from the bridge (deep mode only).
          // VMP entry stubs set VM context registers (R14 = bytecode
          // pointer, etc.) that must be replayed inline at the call site.
          if (!bridge->register_writes.empty()) {
            static constexpr const char *kRegNames[] = {
                "RAX", "RCX", "RDX", "RBX", "RSP", "RBP", "RSI", "RDI",
                "R8",  "R9",  "R10", "R11", "R12", "R13", "R14", "R15",
            };
            for (const auto &rw : bridge->register_writes) {
              if (rw.reg_index >= 16 || rw.reg_index == 4 /*RSP*/)
                continue;
              auto [reg_addr, reg_type] =
                  arch->DefaultLifter(*intrinsics)
                      ->LoadRegAddress(current_block, state_ptr,
                                       kRegNames[rw.reg_index]);
              auto *val = llvm::ConstantInt::get(word_type, rw.value);
              ir.CreateStore(val, reg_addr);
            }
          }

          // Mirror the normal direct-call semantics for the fallthrough:
          // move RETURN_PC into NEXT_PC so the caller resumes at the
          // instruction following the original CALL.
          auto *ret_pc_ref =
              remill::LoadReturnProgramCounterRef(current_block);
          auto *next_pc_ref =
              remill::LoadNextProgramCounterRef(current_block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          EmitDecisionEdge(current_block, fallthrough, fallthrough_target,
                           discovered_targets);
          goto done;
        }

        // Emit: dispatch_call(state, call_target_pc, mem)
        // Then: musttail call @blk_<fallthrough>(state, fallthrough_pc, result)
        {
          const uint64_t call_pc =
              call_target_decision.effective_target_pc
                  ? *call_target_decision.effective_target_pc
                  : call_target;

          // Add the call target to discovered_targets so
          // LiftReachable's BFS lifts the callee's full reachable
          // scope — not just its entry block.  Without this, deep
          // call targets (e.g. VM exit handlers) end up partially
          // lifted with missing successor blocks, which later passes
          // collapse to `body: unreachable`.
          if (call_pc != 0)
            discovered_targets.push_back(call_pc);

          auto *pc_val = llvm::ConstantInt::get(word_type, call_pc);
          auto *lifted_fn_ty = func->getFunctionType();
          auto dispatch = module->getOrInsertFunction(
              canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kCall,
                                             *module),
              lifted_fn_ty);

          auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);

          llvm::IRBuilder<> ir(current_block);
          auto *mp = LoadCurrentMemoryToken(ir, func, *intrinsics);
          auto *call_result = ir.CreateCall(dispatch, {sp, pc_val, mp});

          // Store RETURN_PC into NEXT_PC for the fall-through.
          auto *ret_pc_ref = remill::LoadReturnProgramCounterRef(current_block);
          auto *next_pc_ref = remill::LoadNextProgramCounterRef(current_block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          // Musttail to fall-through block.
          EmitDecisionEdgeWithMemory(current_block, fallthrough,
                                     fallthrough_target, call_result,
                                     discovered_targets);
        }
        goto done;
      }

      case remill::Instruction::kCategoryIndirectFunctionCall: {
        try_add_delay_slot(true, current_block);
        auto fallthrough = inst.branch_not_taken_pc;
        auto fallthrough_target = manager.ResolveLiftTarget(
            current_pc, fallthrough, LiftTargetEdgeKind::kCallFallthrough);

        // Load call target from NEXT_PC (set by instruction semantics).
        auto *call_pc =
            remill::LoadNextProgramCounter(current_block, *intrinsics);

        auto *lifted_fn_ty = func->getFunctionType();
        auto dispatch = module->getOrInsertFunction(
            canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kCall,
                                           *module),
            lifted_fn_ty);

        auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);

        llvm::IRBuilder<> ir(current_block);
        auto *mp = LoadCurrentMemoryToken(ir, func, *intrinsics);
        auto *call_result = ir.CreateCall(dispatch, {sp, call_pc, mp});

        // Store RETURN_PC into NEXT_PC for the fall-through.
        auto *ret_pc_ref = remill::LoadReturnProgramCounterRef(current_block);
        auto *next_pc_ref = remill::LoadNextProgramCounterRef(current_block);
        ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

        // Musttail to fall-through block.
        EmitDecisionEdgeWithMemory(current_block, fallthrough,
                                   fallthrough_target, call_result,
                                   discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryFunctionReturn:
        try_add_delay_slot(true, current_block);
        remill::AddTerminatingTailCall(current_block,
                                       intrinsics->function_return,
                                       *intrinsics);
        goto done;

      case remill::Instruction::kCategoryConditionalFunctionReturn: {
        auto not_taken_pc = inst.branch_not_taken_pc;
        auto not_taken_target = manager.ResolveLiftTarget(
            current_pc, not_taken_pc, LiftTargetEdgeKind::kConditionalNotTaken);

        auto *ret_bb = llvm::BasicBlock::Create(context, "do_ret", func);
        auto *cont_bb = llvm::BasicBlock::Create(context, "no_ret", func);

        if (try_delay) {
          auto *ds_ret = llvm::BasicBlock::Create(context, "ds_ret", func);
          auto *ds_cont = llvm::BasicBlock::Create(context, "ds_cont", func);
          try_add_delay_slot(true, ds_ret);
          try_add_delay_slot(false, ds_cont);
          if (!ds_ret->getTerminator())
            llvm::BranchInst::Create(ret_bb, ds_ret);
          if (!ds_cont->getTerminator())
            llvm::BranchInst::Create(cont_bb, ds_cont);
          llvm::BranchInst::Create(ds_ret, ds_cont,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        } else {
          llvm::BranchInst::Create(ret_bb, cont_bb,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        }

        remill::AddTerminatingTailCall(ret_bb, intrinsics->function_return,
                                       *intrinsics);
        EmitDecisionEdge(cont_bb, not_taken_pc, not_taken_target,
                         discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryConditionalDirectFunctionCall: {
        auto call_target = inst.branch_taken_pc;
        auto fallthrough = inst.branch_not_taken_pc;
        auto fallthrough_target = manager.ResolveLiftTarget(
            current_pc, fallthrough, LiftTargetEdgeKind::kCallFallthrough);
        auto call_target_decision = manager.ResolveLiftTarget(
            current_pc, call_target, LiftTargetEdgeKind::kDirectCallTarget);

        if (call_target == fallthrough) {
          // Degenerate: call target == fall-through.  Just go to fall-through.
          EmitDecisionEdge(current_block, fallthrough, fallthrough_target,
                           discovered_targets);
          goto done;
        }

        auto *do_call_bb =
            llvm::BasicBlock::Create(context, "do_call", func);
        auto *skip_bb =
            llvm::BasicBlock::Create(context, "skip_call", func);

        if (try_delay) {
          auto *ds_call = llvm::BasicBlock::Create(context, "ds_call", func);
          auto *ds_skip = llvm::BasicBlock::Create(context, "ds_skip", func);
          try_add_delay_slot(true, ds_call);
          try_add_delay_slot(false, ds_skip);
          if (!ds_call->getTerminator())
            llvm::BranchInst::Create(do_call_bb, ds_call);
          if (!ds_skip->getTerminator())
            llvm::BranchInst::Create(skip_bb, ds_skip);
          llvm::BranchInst::Create(ds_call, ds_skip,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        } else {
          llvm::BranchInst::Create(do_call_bb, skip_bb,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        }

        // do_call_bb: dispatch_call + musttail to fall-through
        {
          const uint64_t dispatch_pc =
              call_target_decision.effective_target_pc
                  ? *call_target_decision.effective_target_pc
                  : call_target;

          // See kCategoryDirectFunctionCall: add call target so
          // LiftReachable lifts the callee's full reachable scope.
          if (dispatch_pc != 0)
            discovered_targets.push_back(dispatch_pc);

          auto *pc_val = llvm::ConstantInt::get(word_type, dispatch_pc);
          auto *lifted_fn_ty = func->getFunctionType();
          auto dispatch = module->getOrInsertFunction(
              canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kCall,
                                             *module),
              lifted_fn_ty);

          auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);

          llvm::IRBuilder<> ir(do_call_bb);
          auto *mp = LoadCurrentMemoryToken(ir, func, *intrinsics);
          auto *call_result = ir.CreateCall(dispatch, {sp, pc_val, mp});

          auto *ret_pc_ref =
              remill::LoadReturnProgramCounterRef(do_call_bb);
          auto *next_pc_ref =
              remill::LoadNextProgramCounterRef(do_call_bb);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          EmitDecisionEdgeWithMemory(do_call_bb, fallthrough,
                                     fallthrough_target, call_result,
                                     discovered_targets);
        }

        // skip_bb: musttail to fall-through directly
        EmitDecisionEdge(skip_bb, fallthrough, fallthrough_target,
                         discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryConditionalIndirectFunctionCall: {
        auto fallthrough = inst.branch_not_taken_pc;
        auto fallthrough_target = manager.ResolveLiftTarget(
            current_pc, fallthrough, LiftTargetEdgeKind::kCallFallthrough);

        auto *do_call_bb =
            llvm::BasicBlock::Create(context, "do_icall", func);
        auto *skip_bb =
            llvm::BasicBlock::Create(context, "skip_icall", func);

        if (try_delay) {
          auto *ds_call = llvm::BasicBlock::Create(context, "ds_icall", func);
          auto *ds_skip = llvm::BasicBlock::Create(context, "ds_skip", func);
          try_add_delay_slot(true, ds_call);
          try_add_delay_slot(false, ds_skip);
          if (!ds_call->getTerminator())
            llvm::BranchInst::Create(do_call_bb, ds_call);
          if (!ds_skip->getTerminator())
            llvm::BranchInst::Create(skip_bb, ds_skip);
          llvm::BranchInst::Create(ds_call, ds_skip,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        } else {
          llvm::BranchInst::Create(do_call_bb, skip_bb,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        }

        // do_call_bb: dispatch_call + musttail to fall-through
        {
          auto *call_pc =
              remill::LoadNextProgramCounter(do_call_bb, *intrinsics);
          auto *lifted_fn_ty = func->getFunctionType();
          auto dispatch = module->getOrInsertFunction(
              canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kCall,
                                             *module),
              lifted_fn_ty);

          auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);

          llvm::IRBuilder<> ir(do_call_bb);
          auto *mp = LoadCurrentMemoryToken(ir, func, *intrinsics);
          auto *call_result = ir.CreateCall(dispatch, {sp, call_pc, mp});

          auto *ret_pc_ref =
              remill::LoadReturnProgramCounterRef(do_call_bb);
          auto *next_pc_ref =
              remill::LoadNextProgramCounterRef(do_call_bb);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          EmitDecisionEdgeWithMemory(do_call_bb, fallthrough,
                                     fallthrough_target, call_result,
                                     discovered_targets);
        }

        // skip_bb: musttail to fall-through directly
        EmitDecisionEdge(skip_bb, fallthrough, fallthrough_target,
                         discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryConditionalIndirectJump: {
        auto not_taken_pc = inst.branch_not_taken_pc;
        auto not_taken_target = manager.ResolveLiftTarget(
            current_pc, not_taken_pc, LiftTargetEdgeKind::kConditionalNotTaken);

        auto *do_jump_bb =
            llvm::BasicBlock::Create(context, "do_ijmp", func);
        auto *cont_bb =
            llvm::BasicBlock::Create(context, "no_ijmp", func);

        if (try_delay) {
          auto *ds_jump = llvm::BasicBlock::Create(context, "ds_ijmp", func);
          auto *ds_cont =
              llvm::BasicBlock::Create(context, "ds_no_ijmp", func);
          try_add_delay_slot(true, ds_jump);
          try_add_delay_slot(false, ds_cont);
          if (!ds_jump->getTerminator())
            llvm::BranchInst::Create(do_jump_bb, ds_jump);
          if (!ds_cont->getTerminator())
            llvm::BranchInst::Create(cont_bb, ds_cont);
          llvm::BranchInst::Create(ds_jump, ds_cont,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        } else {
          llvm::BranchInst::Create(do_jump_bb, cont_bb,
                                   remill::LoadBranchTaken(current_block),
                                   current_block);
        }

        EmitDispatchJump(do_jump_bb);
        EmitDecisionEdge(cont_bb, not_taken_pc, not_taken_target,
                         discovered_targets);
        goto done;
      }

      case remill::Instruction::kCategoryAsyncHyperCall: {
        remill::AddTerminatingTailCall(current_block,
                                       intrinsics->async_hyper_call,
                                       *intrinsics);
        goto done;
      }

      case remill::Instruction::kCategoryConditionalAsyncHyperCall: {
        auto next_pc = inst.next_pc;
        auto next_target = manager.ResolveLiftTarget(
            current_pc, next_pc, LiftTargetEdgeKind::kTraceNext);

        auto *do_hyper =
            llvm::BasicBlock::Create(context, "do_hyper", func);
        auto *cont_bb =
            llvm::BasicBlock::Create(context, "no_hyper", func);

        llvm::BranchInst::Create(do_hyper, cont_bb,
                                 remill::LoadBranchTaken(current_block),
                                 current_block);

        remill::AddTerminatingTailCall(do_hyper,
                                       intrinsics->async_hyper_call,
                                       *intrinsics);
        EmitDecisionEdge(cont_bb, next_pc, next_target, discovered_targets);
        goto done;
      }
    }

    // If we get here, unhandled category.
    remill::AddTerminatingTailCall(current_block, intrinsics->error,
                                   *intrinsics);
    break;
    }
  } __except (1) {
    lift_crashed = true;
  }

  if (lift_crashed) {
    llvm::errs() << "omill: BlockLifter: crashed while lifting block at 0x"
                 << llvm::Twine::utohexstr(addr) << "\n";
    func->deleteBody();
    return nullptr;
  }

done:
  // Seal any unterminated blocks.
  for (auto &bb : *func) {
    if (!bb.getTerminator()) {
      if (invalidated_block_entry) {
        EmitMusttailToMissingBlock(
            &bb, addr,
            invalidated_block_decision ? &*invalidated_block_decision
                                       : nullptr);
      } else {
        remill::AddTerminatingTailCall(&bb, intrinsics->missing_block,
                                       *intrinsics);
      }
    }
  }

  PopulateProjectedTargets(addr, discovered_targets);
  manager.SetLiftedBlockDefinition(addr, func);
  return func;
}

// ---------------------------------------------------------------------------
// LiftReachable — BFS over statically-known successors
// ---------------------------------------------------------------------------

unsigned BlockLifter::Impl::LiftReachable(uint64_t addr) {
  std::queue<uint64_t> worklist;
  std::set<uint64_t> visited;
  unsigned count = 0;

  worklist.push(addr);
  visited.insert(addr);

  while (!worklist.empty()) {
    auto pc = worklist.front();
    worklist.pop();

    llvm::SmallVector<uint64_t, 4> successors;
    auto *fn = LiftBlock(pc, successors);
    if (!fn) {
      continue;
    }
    ++count;

    for (auto succ_pc : successors) {
      if (visited.insert(succ_pc).second) {
        worklist.push(succ_pc);
      }
    }
  }

  return count;
}

// ---------------------------------------------------------------------------
// BlockLifter public API
// ---------------------------------------------------------------------------

BlockLifter::~BlockLifter() {}

BlockLifter::BlockLifter(const remill::Arch *arch, BlockManager &manager)
    : impl(new Impl(arch, manager)) {}

void BlockLifter::SetLiftDatabase(const LiftDatabase *db) {
  impl->SetLiftDatabase(db);
}

llvm::Function *BlockLifter::LiftBlock(
    uint64_t addr,
    llvm::SmallVectorImpl<uint64_t> &discovered_targets) {
  return impl->LiftBlock(addr, discovered_targets);
}

unsigned BlockLifter::LiftReachable(uint64_t addr) {
  return impl->LiftReachable(addr);
}

llvm::Module *BlockLifter::GetModule() const {
  return impl->GetModule();
}

}  // namespace omill
