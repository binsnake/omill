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

namespace omill {

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

// ---------------------------------------------------------------------------
// TraceLifter::Impl
// ---------------------------------------------------------------------------

namespace {
using DecoderWorkList = std::set<uint64_t>;  // Ordered for determinism.
}  // namespace

class TraceLifter::Impl {
 public:
  Impl(const remill::Arch *arch_, TraceManager *manager_);

  bool Lift(uint64_t addr,
            std::function<void(uint64_t, llvm::Function *)> callback);

  bool ReadInstructionBytes(uint64_t addr);

  llvm::Function *GetLiftedTraceDeclaration(uint64_t addr);
  llvm::Function *GetLiftedTraceDefinition(uint64_t addr);

  llvm::BasicBlock *GetOrCreateBlock(uint64_t block_pc) {
    auto &block = blocks[block_pc];
    if (!block) {
      // Only name blocks that came from devirtualized targets (jump table
      // analysis).  Naming ALL blocks block_<hex> would confuse omill passes
      // that use extractBlockPC / collectBlockPCMap throughout the pipeline.
      std::string name;
      if (devirt_targets.count(block_pc)) {
        std::stringstream ss;
        ss << "block_" << std::hex << block_pc;
        name = ss.str();
      }
      block = llvm::BasicBlock::Create(context, name, func);
    }
    return block;
  }

  llvm::BasicBlock *GetOrCreateBranchTakenBlock() {
    inst_work_list.insert(inst.branch_taken_pc);
    return GetOrCreateBlock(inst.branch_taken_pc);
  }

  llvm::BasicBlock *GetOrCreateBranchNotTakenBlock() {
    assert(inst.branch_not_taken_pc != 0 &&
           "branch_not_taken_pc must be non-zero");
    inst_work_list.insert(inst.branch_not_taken_pc);
    return GetOrCreateBlock(inst.branch_not_taken_pc);
  }

  llvm::BasicBlock *GetOrCreateNextBlock() {
    inst_work_list.insert(inst.next_pc);
    return GetOrCreateBlock(inst.next_pc);
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
  std::map<uint64_t, llvm::BasicBlock *> blocks;
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
  blocks.clear();
  inst_bytes.clear();
  func = nullptr;
  switch_inst = nullptr;
  block = nullptr;
  inst.Reset();
  delayed_inst.Reset();

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

    // Already lifted.
    func = GetLiftedTraceDefinition(trace_addr);
    if (func) {
      continue;
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
    inst_work_list.insert(trace_addr);

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

      auto decode_ok = arch->DecodeInstruction(
          inst_addr, inst_bytes, inst, this->arch->CreateInitialContext());
      if (!decode_ok) {
        llvm::errs() << "omill: TraceLifter: decode failed at 0x"
                     << llvm::Twine::utohexstr(inst_addr) << "\n";
      }

      auto lift_status =
          inst.GetLifter()->LiftIntoBlock(inst, block, state_ptr);
      if (remill::kLiftedInstruction != lift_status) {
        remill::AddTerminatingTailCall(block, intrinsics->error, *intrinsics);
        continue;
      }

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
          llvm::BranchInst::Create(GetOrCreateNextBlock(), block);
          break;

        case remill::Instruction::kCategoryDirectJump:
          try_add_delay_slot(true, block);
          llvm::BranchInst::Create(GetOrCreateBranchTakenBlock(), block);
          break;

        case remill::Instruction::kCategoryIndirectJump: {
          try_add_delay_slot(true, block);
          remill::AddTerminatingTailCall(block, intrinsics->jump, *intrinsics);

          // Ask the trace manager for devirtualized targets (e.g. from
          // binary-level jump table analysis).
          manager.ForEachDevirtualizedTarget(
              inst,
              [this](uint64_t target, DevirtualizedTargetKind) {
                inst_work_list.insert(target);
                devirt_targets.insert(target);
              });
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
          ir.CreateBr(GetOrCreateBranchNotTakenBlock());

          remill::AddCall(block, intrinsics->function_call, *intrinsics);
          llvm::BranchInst::Create(fall_through_block, block);
          block = fall_through_block;
          continue;
        }

        case remill::Instruction::kCategoryConditionalIndirectFunctionCall: {
          auto taken_block = llvm::BasicBlock::Create(context, "", func);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock();
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
            trace_work_list.insert(inst.branch_taken_pc);
            auto target_trace = get_trace_decl(inst.branch_taken_pc);
            remill::AddCall(block, target_trace, *intrinsics);
          }

          const auto ret_pc_ref =
              remill::LoadReturnProgramCounterRef(block);
          const auto next_pc_ref =
              remill::LoadNextProgramCounterRef(block);
          llvm::IRBuilder<> ir(block);
          ir.CreateStore(ir.CreateLoad(word_type, ret_pc_ref), next_pc_ref);
          ir.CreateBr(GetOrCreateBranchNotTakenBlock());
          continue;
        }

        case remill::Instruction::kCategoryConditionalDirectFunctionCall: {
          if (inst.branch_not_taken_pc == inst.branch_taken_pc) {
            goto direct_func_call;
          }

          auto taken_block = llvm::BasicBlock::Create(context, "", func);
          auto not_taken_block = GetOrCreateBranchNotTakenBlock();
          const auto orig_not_taken_block = not_taken_block;

          if (try_delay) {
            not_taken_block = llvm::BasicBlock::Create(context, "", func);
            try_add_delay_slot(true, taken_block);
            try_add_delay_slot(false, not_taken_block);
            llvm::BranchInst::Create(orig_not_taken_block, not_taken_block);
          }

          llvm::BranchInst::Create(taken_block, not_taken_block,
                                   remill::LoadBranchTaken(block), block);

          trace_work_list.insert(inst.branch_taken_pc);
          auto target_trace = get_trace_decl(inst.branch_taken_pc);

          remill::AddCall(taken_block, intrinsics->function_call, *intrinsics);
          remill::AddCall(taken_block, target_trace, *intrinsics);

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
          llvm::BranchInst::Create(do_hyper_call, GetOrCreateNextBlock(),
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
            ir.CreateCondBr(eq, GetOrCreateNextBlock(), unexpected_ret_pc);
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
          auto not_taken_block = GetOrCreateBranchNotTakenBlock();
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
          auto taken_block = GetOrCreateBranchTakenBlock();
          auto not_taken_block = GetOrCreateBranchNotTakenBlock();

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
          auto not_taken_block = GetOrCreateBranchNotTakenBlock();
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

  return true;
}

}  // namespace omill
