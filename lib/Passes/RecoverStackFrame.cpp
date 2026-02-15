#include "omill/Passes/RecoverStackFrame.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <algorithm>

namespace omill {

namespace {

/// Try to trace a value back to base_val + constant_offset.
bool traceToBase(llvm::Value *addr, llvm::Value *base_val, int64_t &offset) {
  if (addr == base_val) {
    offset = 0;
    return true;
  }

  if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(addr)) {
    auto opcode = binop->getOpcode();
    if (opcode == llvm::Instruction::Add) {
      if (binop->getOperand(0) == base_val) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
          offset = CI->getSExtValue();
          return true;
        }
      }
      if (binop->getOperand(1) == base_val) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(0))) {
          offset = CI->getSExtValue();
          return true;
        }
      }
    }
    if (opcode == llvm::Instruction::Sub) {
      if (binop->getOperand(0) == base_val) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
          offset = -CI->getSExtValue();
          return true;
        }
      }
    }
  }

  return false;
}

/// Check if a value is derived from base_val through arithmetic operations.
/// Walks through chains of add/sub/or/and/shl/lshr and trunc/zext/sext casts.
/// This handles SROA decompose/reassemble patterns where a register value is
/// split into sub-fields (trunc/and/lshr) and reassembled (shl/or/zext).
bool isDerivedFrom(llvm::Value *V, llvm::Value *base_val,
                   unsigned depth = 0) {
  if (depth > 16) return false;
  if (V == base_val) return true;

  if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto opcode = binop->getOpcode();
    if (opcode == llvm::Instruction::Add ||
        opcode == llvm::Instruction::Sub ||
        opcode == llvm::Instruction::Or ||
        opcode == llvm::Instruction::And ||
        opcode == llvm::Instruction::Shl ||
        opcode == llvm::Instruction::LShr ||
        opcode == llvm::Instruction::AShr) {
      return isDerivedFrom(binop->getOperand(0), base_val, depth + 1) ||
             isDerivedFrom(binop->getOperand(1), base_val, depth + 1);
    }
  }

  if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V)) {
    auto opcode = CI->getOpcode();
    if (opcode == llvm::Instruction::Trunc ||
        opcode == llvm::Instruction::ZExt ||
        opcode == llvm::Instruction::SExt) {
      return isDerivedFrom(CI->getOperand(0), base_val, depth + 1);
    }
  }

  return false;
}

/// Resolve the byte offset of a GEP from the State pointer (arg0).
/// Returns -1 if the pointer doesn't originate from State.
int64_t resolveStateGEPOffset(llvm::Value *ptr, llvm::Value *state_ptr,
                              const llvm::DataLayout &DL) {
  llvm::Value *base = ptr;
  int64_t total_offset = 0;
  while (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
    llvm::APInt ap_offset(64, 0);
    if (!GEP->accumulateConstantOffset(DL, ap_offset))
      return -1;
    total_offset += ap_offset.getSExtValue();
    base = GEP->getPointerOperand();
  }
  return (base == state_ptr) ? total_offset : -1;
}

/// Check if a load has any constant-offset inttoptr user.
bool hasIntToPtrUser(llvm::LoadInst *LI) {
  for (auto *user : LI->users()) {
    if (llvm::isa<llvm::IntToPtrInst>(user))
      return true;
    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
      int64_t offset = 0;
      if (traceToBase(binop, LI, offset)) {
        for (auto *bu : binop->users()) {
          if (llvm::isa<llvm::IntToPtrInst>(bu))
            return true;
        }
      }
    }
  }
  return false;
}

/// Find loads from the State struct whose values are used as memory base
/// pointers through inttoptr patterns.
///
/// Two-pass approach:
///   1. Find State field offsets that have at least one load with a NEGATIVE
///      constant offset through inttoptr (identifies the stack pointer field).
///   2. Collect ALL loads from those State field offsets that have ANY
///      inttoptr usage (captures both pre-SUB and post-SUB RSP values).
llvm::SmallVector<llvm::LoadInst *, 4> findStackBaseLoads(
    llvm::Function &F) {
  llvm::SmallVector<llvm::LoadInst *, 4> result;

  if (F.arg_empty()) return result;
  llvm::Value *state_ptr = F.getArg(0);
  auto &DL = F.getDataLayout();

  // Pass 1: find State field offsets with negative-offset inttoptr patterns.
  llvm::DenseSet<int64_t> stack_field_offsets;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64)) continue;

      int64_t state_off = resolveStateGEPOffset(
          LI->getPointerOperand(), state_ptr, DL);
      if (state_off < 0) continue;

      for (auto *user : LI->users()) {
        if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
          int64_t offset = 0;
          if (traceToBase(binop, LI, offset) && offset < 0) {
            for (auto *bu : binop->users()) {
              if (llvm::isa<llvm::IntToPtrInst>(bu)) {
                stack_field_offsets.insert(state_off);
                break;
              }
            }
          }
        }
        if (stack_field_offsets.count(state_off)) break;
      }
    }
  }

  if (stack_field_offsets.empty()) return result;

  // Pass 2: collect ALL loads from those State field offsets that have
  // inttoptr users (positive or negative offsets).
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64)) continue;

      int64_t state_off = resolveStateGEPOffset(
          LI->getPointerOperand(), state_ptr, DL);
      if (state_off < 0 || !stack_field_offsets.count(state_off)) continue;

      if (hasIntToPtrUser(LI)) {
        result.push_back(LI);
      }
    }
  }

  return result;
}

/// Collect constant inttoptr offsets from a base load.
llvm::SmallVector<int64_t, 16> collectIntToPtrOffsets(
    llvm::LoadInst *base_load) {
  llvm::SmallVector<int64_t, 16> offsets;
  for (auto *user : base_load->users()) {
    if (llvm::isa<llvm::IntToPtrInst>(user)) {
      offsets.push_back(0);
      continue;
    }
    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
      int64_t offset = 0;
      if (traceToBase(binop, base_load, offset)) {
        bool has_itp = false;
        for (auto *bu : binop->users()) {
          if (llvm::isa<llvm::IntToPtrInst>(bu)) { has_itp = true; break; }
        }
        if (has_itp) offsets.push_back(offset);
      }
    }
  }
  return offsets;
}

/// A contiguous region of the stack frame.
struct FrameRegion {
  int64_t min_offset;
  int64_t max_offset;
};

/// Group sorted offsets into contiguous regions.
/// Offsets within `gap` bytes of each other are in the same region.
llvm::SmallVector<FrameRegion, 4> clusterOffsets(
    llvm::SmallVector<int64_t, 16> &offsets, int64_t gap = 16) {
  llvm::SmallVector<FrameRegion, 4> regions;
  if (offsets.empty()) return regions;

  llvm::sort(offsets);
  // Remove duplicates.
  offsets.erase(std::unique(offsets.begin(), offsets.end()), offsets.end());

  int64_t cur_min = offsets[0];
  int64_t cur_max = offsets[0];

  for (size_t i = 1; i < offsets.size(); ++i) {
    if (offsets[i] - cur_max > gap) {
      regions.push_back({cur_min, cur_max});
      cur_min = offsets[i];
    }
    cur_max = offsets[i];
  }
  regions.push_back({cur_min, cur_max});
  return regions;
}

/// Collect all inttoptr instructions in the function whose operands are
/// derived from the given base load (through any arithmetic chain).
llvm::SmallVector<llvm::IntToPtrInst *, 16> collectDerivedIntToPtr(
    llvm::Function &F, llvm::LoadInst *base_load) {
  llvm::SmallVector<llvm::IntToPtrInst *, 16> result;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&I)) {
        if (isDerivedFrom(ITP->getOperand(0), base_load)) {
          result.push_back(ITP);
        }
      }
    }
  }
  return result;
}

}  // namespace

llvm::PreservedAnalyses RecoverStackFramePass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration() || F.empty() || F.arg_size() == 0) {
    return llvm::PreservedAnalyses::all();
  }

  auto base_loads = findStackBaseLoads(F);
  if (base_loads.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  auto *i8_ty = EntryBuilder.getInt8Ty();
  auto *i64_ty = EntryBuilder.getInt64Ty();
  bool changed = false;

  for (auto *base_load : base_loads) {
    // Collect all constant inttoptr offsets from this base load.
    auto offsets = collectIntToPtrOffsets(base_load);
    if (offsets.empty()) continue;

    // Group offsets into contiguous regions (gap > 16 bytes = separate region).
    auto regions = clusterOffsets(offsets, 16);

    // Create a separate alloca for each region.
    for (auto &region : regions) {
      int64_t min_off = region.min_offset;
      int64_t max_off = region.max_offset;
      int64_t frame_size = max_off - min_off + 8;
      if (frame_size <= 0) frame_size = 8;

      auto *frame_ty = llvm::ArrayType::get(i8_ty, frame_size);
      auto *frame_alloca = EntryBuilder.CreateAlloca(frame_ty, nullptr,
                                                      "stack_frame");

      // Replace inttoptr instructions whose constant offset falls in this
      // region.
      auto int_to_ptrs = collectDerivedIntToPtr(F, base_load);

      for (auto *itp : int_to_ptrs) {
        llvm::Value *operand = itp->getOperand(0);
        int64_t const_off = 0;
        if (!traceToBase(operand, base_load, const_off)) continue;
        if (const_off < min_off || const_off > max_off) continue;

        llvm::IRBuilder<> Builder(itp);
        auto *alloca_idx = llvm::ConstantInt::get(i64_ty,
                                                    const_off - min_off);
        auto *gep = Builder.CreateGEP(i8_ty, frame_alloca, alloca_idx,
                                       "frame_ptr");
        itp->replaceAllUsesWith(gep);
        itp->eraseFromParent();
        changed = true;
      }

      // Replace bare add(RSP, C) values whose offset falls in this region
      // with ptrtoint(GEP).  This ties the buffer address to the alloca,
      // preventing SROA from decomposing the xorstr buffer region.
      {
        llvm::SmallVector<llvm::BinaryOperator *, 8> bare_ops;
        for (auto *user : base_load->users()) {
          auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user);
          if (!binop) continue;
          int64_t offset = 0;
          if (!traceToBase(binop, base_load, offset)) continue;
          if (binop->use_empty()) continue;
          if (offset < min_off || offset > max_off) continue;
          // Skip if any user is an inttoptr (not yet replaced or in another
          // region).
          bool has_itp = false;
          for (auto *bu : binop->users()) {
            if (llvm::isa<llvm::IntToPtrInst>(bu)) { has_itp = true; break; }
          }
          if (has_itp) continue;
          bare_ops.push_back(binop);
        }

        for (auto *binop : bare_ops) {
          int64_t offset = 0;
          traceToBase(binop, base_load, offset);
          int64_t idx = offset - min_off;
          llvm::IRBuilder<> Builder(binop->getNextNode());
          auto *gep = Builder.CreateGEP(i8_ty, frame_alloca,
              llvm::ConstantInt::get(i64_ty, idx), "frame_addr");
          auto *pti = Builder.CreatePtrToInt(gep, i64_ty, "frame_int");
          binop->replaceAllUsesWith(pti);
          binop->eraseFromParent();
          changed = true;
        }
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
