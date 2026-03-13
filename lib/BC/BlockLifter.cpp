/// \file BlockLifter.cpp
/// \brief Per-basic-block lifter for iterative target resolution.
///
/// See include/omill/BC/BlockLifter.h for design rationale.

#include "omill/BC/BlockLifter.h"

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
#include <queue>
#include <set>
#include <sstream>

namespace omill {

// ---------------------------------------------------------------------------
// BlockManager default implementations
// ---------------------------------------------------------------------------

BlockManager::~BlockManager() {}

std::string BlockManager::BlockName(uint64_t addr) {
  std::stringstream ss;
  ss << "blk_" << std::hex << addr;
  return ss.str();
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

  llvm::Module *GetModule() const { return module; }

 private:
  bool ReadInstructionBytes(uint64_t addr);

  /// Declare a block-function (empty declaration with lifted signature).
  llvm::Function *DeclareBlockFunction(uint64_t addr);

  /// Get existing declaration or create one.
  llvm::Function *GetOrDeclareBlockFunction(uint64_t addr);

  /// Emit a musttail call to a block-function and ret.
  /// This is the standard inter-block transfer for direct jumps/branches.
  void EmitMusttailToBlock(llvm::BasicBlock *from_bb,
                           llvm::Function *target_fn,
                           uint64_t target_pc);

  /// Emit a call to __omill_dispatch_jump for unresolved indirect jumps.
  void EmitDispatchJump(llvm::BasicBlock *bb);

  /// Emit a call to __omill_dispatch_call + musttail to fall-through block.
  void EmitDispatchCallAndFallthrough(llvm::BasicBlock *bb,
                                      uint64_t fallthrough_pc,
                                      llvm::SmallVectorImpl<uint64_t> &targets);

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
  return DeclareBlockFunction(addr);
}

// ---------------------------------------------------------------------------
// Terminator emission
// ---------------------------------------------------------------------------

void BlockLifter::Impl::EmitMusttailToBlock(llvm::BasicBlock *from_bb,
                                             llvm::Function *target_fn,
                                             uint64_t target_pc) {
  auto *func = from_bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
  auto *mem_ptr = remill::NthArgument(func, remill::kMemoryPointerArgNum);

  llvm::IRBuilder<> ir(from_bb);
  auto *pc_val = llvm::ConstantInt::get(word_type, target_pc);
  auto *call = ir.CreateCall(target_fn->getFunctionType(), target_fn,
                             {state_ptr, pc_val, mem_ptr});
  call->setTailCallKind(llvm::CallInst::TCK_MustTail);
  ir.CreateRet(call);
}

void BlockLifter::Impl::EmitDispatchJump(llvm::BasicBlock *bb) {
  auto *func = bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
  auto *mem_ptr = remill::NthArgument(func, remill::kMemoryPointerArgNum);

  // Load the computed target PC from NEXT_PC (set by instruction semantics).
  auto *next_pc = remill::LoadNextProgramCounter(bb, *intrinsics);

  // Get or create __omill_dispatch_jump.
  auto *lifted_fn_ty = func->getFunctionType();
  auto dispatch = module->getOrInsertFunction("__omill_dispatch_jump",
                                              lifted_fn_ty);

  llvm::IRBuilder<> ir(bb);
  auto *result = ir.CreateCall(dispatch, {state_ptr, next_pc, mem_ptr});
  ir.CreateRet(result);
}

void BlockLifter::Impl::EmitDispatchCallAndFallthrough(
    llvm::BasicBlock *bb,
    uint64_t fallthrough_pc,
    llvm::SmallVectorImpl<uint64_t> &targets) {
  auto *func = bb->getParent();
  auto *state_ptr = remill::NthArgument(func, remill::kStatePointerArgNum);
  auto *mem_ptr = remill::NthArgument(func, remill::kMemoryPointerArgNum);

  // Load the target PC for the call.
  auto *call_pc = remill::LoadNextProgramCounter(bb, *intrinsics);

  // Get or create __omill_dispatch_call.
  auto *lifted_fn_ty = func->getFunctionType();
  auto dispatch = module->getOrInsertFunction("__omill_dispatch_call",
                                              lifted_fn_ty);

  llvm::IRBuilder<> ir(bb);
  auto *call_result = ir.CreateCall(dispatch, {state_ptr, call_pc, mem_ptr});

  // The call returns Memory*.  Now musttail to the fall-through block.
  targets.push_back(fallthrough_pc);
  auto *ft_fn = GetOrDeclareBlockFunction(fallthrough_pc);
  auto *ft_pc = llvm::ConstantInt::get(word_type, fallthrough_pc);
  auto *ft_call = ir.CreateCall(ft_fn->getFunctionType(), ft_fn,
                                {state_ptr, ft_pc, call_result});
  ft_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
  ir.CreateRet(ft_call);
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

  while (true) {
    // No executable bytes?
    if (!ReadInstructionBytes(current_pc)) {
      remill::AddTerminatingTailCall(current_block, intrinsics->missing_block,
                                     *intrinsics);
      break;
    }

    inst.Reset();
    auto decode_ok = arch->DecodeInstruction(current_pc, inst_bytes, inst,
                                              arch->CreateInitialContext());
    if (!decode_ok) {
      llvm::errs() << "omill: BlockLifter: decode failed at 0x"
                   << llvm::Twine::utohexstr(current_pc) << "\n";
    }

    auto lift_status =
        inst.GetLifter()->LiftIntoBlock(inst, current_block, state_ptr);
    if (remill::kLiftedInstruction != lift_status) {
      remill::AddTerminatingTailCall(current_block, intrinsics->error,
                                     *intrinsics);
      break;
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
        discovered_targets.push_back(target);
        auto *target_fn = GetOrDeclareBlockFunction(target);
        EmitMusttailToBlock(current_block, target_fn, target);
        goto done;
      }

      case remill::Instruction::kCategoryIndirectJump: {
        try_add_delay_slot(true, current_block);
        EmitDispatchJump(current_block);

        // Ask the manager for devirtualized targets.
        manager.ForEachDevirtualizedTarget(
            inst,
            [&](uint64_t target, DevirtualizedTargetKind) {
              discovered_targets.push_back(target);
            });
        goto done;
      }

      case remill::Instruction::kCategoryConditionalBranch: {
        auto taken_pc = inst.branch_taken_pc;
        auto not_taken_pc = inst.branch_not_taken_pc;

        discovered_targets.push_back(taken_pc);
        discovered_targets.push_back(not_taken_pc);

        auto *taken_fn = GetOrDeclareBlockFunction(taken_pc);
        auto *not_taken_fn = GetOrDeclareBlockFunction(not_taken_pc);

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

        EmitMusttailToBlock(taken_bb, taken_fn, taken_pc);
        EmitMusttailToBlock(not_taken_bb, not_taken_fn, not_taken_pc);
        goto done;
      }

      case remill::Instruction::kCategoryDirectFunctionCall: {
        try_add_delay_slot(true, current_block);
        auto call_target = inst.branch_taken_pc;
        auto fallthrough = inst.branch_not_taken_pc;

        // Emit: dispatch_call(state, call_target_pc, mem)
        // Then: musttail call @blk_<fallthrough>(state, fallthrough_pc, result)
        {
          auto *pc_val = llvm::ConstantInt::get(word_type, call_target);
          auto *lifted_fn_ty = func->getFunctionType();
          auto dispatch = module->getOrInsertFunction(
              "__omill_dispatch_call", lifted_fn_ty);

          auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);
          auto *mp = remill::NthArgument(func, remill::kMemoryPointerArgNum);

          llvm::IRBuilder<> ir(current_block);
          auto *call_result = ir.CreateCall(dispatch, {sp, pc_val, mp});

          // Store RETURN_PC into NEXT_PC for the fall-through.
          auto *ret_pc_ref = remill::LoadReturnProgramCounterRef(current_block);
          auto *next_pc_ref = remill::LoadNextProgramCounterRef(current_block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          // Musttail to fall-through block.
          discovered_targets.push_back(fallthrough);
          auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
          auto *ft_pc = llvm::ConstantInt::get(word_type, fallthrough);
          auto *ft_call = ir.CreateCall(ft_fn->getFunctionType(), ft_fn,
                                        {sp, ft_pc, call_result});
          ft_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
          ir.CreateRet(ft_call);
        }
        goto done;
      }

      case remill::Instruction::kCategoryIndirectFunctionCall: {
        try_add_delay_slot(true, current_block);
        auto fallthrough = inst.branch_not_taken_pc;

        // Load call target from NEXT_PC (set by instruction semantics).
        auto *call_pc =
            remill::LoadNextProgramCounter(current_block, *intrinsics);

        auto *lifted_fn_ty = func->getFunctionType();
        auto dispatch = module->getOrInsertFunction(
            "__omill_dispatch_call", lifted_fn_ty);

        auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);
        auto *mp = remill::NthArgument(func, remill::kMemoryPointerArgNum);

        llvm::IRBuilder<> ir(current_block);
        auto *call_result = ir.CreateCall(dispatch, {sp, call_pc, mp});

        // Store RETURN_PC into NEXT_PC for the fall-through.
        auto *ret_pc_ref = remill::LoadReturnProgramCounterRef(current_block);
        auto *next_pc_ref = remill::LoadNextProgramCounterRef(current_block);
        ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

        // Musttail to fall-through block.
        discovered_targets.push_back(fallthrough);
        auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
        auto *ft_pc = llvm::ConstantInt::get(word_type, fallthrough);
        auto *ft_call = ir.CreateCall(ft_fn->getFunctionType(), ft_fn,
                                      {sp, ft_pc, call_result});
        ft_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
        ir.CreateRet(ft_call);
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
        discovered_targets.push_back(not_taken_pc);

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
        auto *cont_fn = GetOrDeclareBlockFunction(not_taken_pc);
        EmitMusttailToBlock(cont_bb, cont_fn, not_taken_pc);
        goto done;
      }

      case remill::Instruction::kCategoryConditionalDirectFunctionCall: {
        auto call_target = inst.branch_taken_pc;
        auto fallthrough = inst.branch_not_taken_pc;
        discovered_targets.push_back(fallthrough);

        if (call_target == fallthrough) {
          // Degenerate: call target == fall-through.  Just go to fall-through.
          auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
          EmitMusttailToBlock(current_block, ft_fn, fallthrough);
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
          auto *pc_val = llvm::ConstantInt::get(word_type, call_target);
          auto *lifted_fn_ty = func->getFunctionType();
          auto dispatch = module->getOrInsertFunction(
              "__omill_dispatch_call", lifted_fn_ty);

          auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);
          auto *mp = remill::NthArgument(func, remill::kMemoryPointerArgNum);

          llvm::IRBuilder<> ir(do_call_bb);
          auto *call_result = ir.CreateCall(dispatch, {sp, pc_val, mp});

          auto *ret_pc_ref =
              remill::LoadReturnProgramCounterRef(do_call_bb);
          auto *next_pc_ref =
              remill::LoadNextProgramCounterRef(do_call_bb);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
          auto *ft_pc = llvm::ConstantInt::get(word_type, fallthrough);
          auto *ft_call = ir.CreateCall(ft_fn->getFunctionType(), ft_fn,
                                        {sp, ft_pc, call_result});
          ft_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
          ir.CreateRet(ft_call);
        }

        // skip_bb: musttail to fall-through directly
        {
          auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
          EmitMusttailToBlock(skip_bb, ft_fn, fallthrough);
        }
        goto done;
      }

      case remill::Instruction::kCategoryConditionalIndirectFunctionCall: {
        auto fallthrough = inst.branch_not_taken_pc;
        discovered_targets.push_back(fallthrough);

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
              "__omill_dispatch_call", lifted_fn_ty);

          auto *sp = remill::NthArgument(func, remill::kStatePointerArgNum);
          auto *mp = remill::NthArgument(func, remill::kMemoryPointerArgNum);

          llvm::IRBuilder<> ir(do_call_bb);
          auto *call_result = ir.CreateCall(dispatch, {sp, call_pc, mp});

          auto *ret_pc_ref =
              remill::LoadReturnProgramCounterRef(do_call_bb);
          auto *next_pc_ref =
              remill::LoadNextProgramCounterRef(do_call_bb);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);

          auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
          auto *ft_pc = llvm::ConstantInt::get(word_type, fallthrough);
          auto *ft_call = ir.CreateCall(ft_fn->getFunctionType(), ft_fn,
                                        {sp, ft_pc, call_result});
          ft_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
          ir.CreateRet(ft_call);
        }

        // skip_bb: musttail to fall-through directly
        {
          auto *ft_fn = GetOrDeclareBlockFunction(fallthrough);
          EmitMusttailToBlock(skip_bb, ft_fn, fallthrough);
        }
        goto done;
      }

      case remill::Instruction::kCategoryConditionalIndirectJump: {
        auto not_taken_pc = inst.branch_not_taken_pc;
        discovered_targets.push_back(not_taken_pc);

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
        auto *cont_fn = GetOrDeclareBlockFunction(not_taken_pc);
        EmitMusttailToBlock(cont_bb, cont_fn, not_taken_pc);
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
        discovered_targets.push_back(next_pc);

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
        auto *cont_fn = GetOrDeclareBlockFunction(next_pc);
        EmitMusttailToBlock(cont_bb, cont_fn, next_pc);
        goto done;
      }
    }

    // If we get here, unhandled category.
    remill::AddTerminatingTailCall(current_block, intrinsics->error,
                                   *intrinsics);
    break;
  }

done:
  // Seal any unterminated blocks.
  for (auto &bb : *func) {
    if (!bb.getTerminator()) {
      remill::AddTerminatingTailCall(&bb, intrinsics->missing_block,
                                     *intrinsics);
    }
  }

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
