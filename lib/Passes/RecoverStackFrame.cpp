#include "omill/Passes/RecoverStackFrame.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

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

/// Find loads from the State struct (first argument) whose values are used
/// as memory base pointers with negative constant offsets (stack pointer).
llvm::SmallVector<llvm::LoadInst *, 4> findStackBaseLoads(
    llvm::Function &F) {
  llvm::SmallVector<llvm::LoadInst *, 4> result;

  if (F.arg_empty()) return result;
  llvm::Value *state_ptr = F.getArg(0);

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64)) continue;

      auto *ptr_op = LI->getPointerOperand();
      llvm::Value *base = ptr_op;
      if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base))
        base = GEP->getPointerOperand();
      if (base != state_ptr) continue;

      // Require at least one negative constant offset → inttoptr pattern.
      bool has_negative_offset = false;
      for (auto *user : LI->users()) {
        if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
          int64_t offset = 0;
          if (traceToBase(binop, LI, offset) && offset < 0) {
            for (auto *binop_user : binop->users()) {
              if (llvm::isa<llvm::IntToPtrInst>(binop_user)) {
                has_negative_offset = true;
                break;
              }
            }
          }
        }
        if (has_negative_offset) break;
      }

      if (has_negative_offset) {
        result.push_back(LI);
      }
    }
  }

  return result;
}

/// Scan constant-offset inttoptr patterns to determine frame bounds.
void computeFrameBounds(llvm::LoadInst *base_load,
                        int64_t &min_offset, int64_t &max_offset) {
  for (auto *user : base_load->users()) {
    if (llvm::isa<llvm::IntToPtrInst>(user)) {
      if (0 < min_offset) min_offset = 0;
      if (0 > max_offset) max_offset = 0;
      continue;
    }

    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
      int64_t offset = 0;
      if (traceToBase(binop, base_load, offset)) {
        for (auto *binop_user : binop->users()) {
          if (llvm::isa<llvm::IntToPtrInst>(binop_user)) {
            if (offset < min_offset) min_offset = offset;
            if (offset > max_offset) max_offset = offset;
          }
        }
      }
    }
  }
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

  // Compute frame bounds from constant-offset patterns.
  int64_t min_offset = 0;
  int64_t max_offset = 0;
  for (auto *base_load : base_loads) {
    computeFrameBounds(base_load, min_offset, max_offset);
  }

  // Create a stack frame alloca.
  int64_t frame_size = max_offset - min_offset + 8;
  if (frame_size <= 0) frame_size = 8;

  llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  auto *i8_ty = EntryBuilder.getInt8Ty();
  auto *i64_ty = EntryBuilder.getInt64Ty();
  auto *frame_ty = llvm::ArrayType::get(i8_ty, frame_size);
  auto *frame_alloca = EntryBuilder.CreateAlloca(frame_ty, nullptr, "stack_frame");

  bool changed = false;

  for (auto *base_load : base_loads) {
    // Collect ALL inttoptr instructions derived from this RSP load.
    auto int_to_ptrs = collectDerivedIntToPtr(F, base_load);

    for (auto *itp : int_to_ptrs) {
      llvm::Value *operand = itp->getOperand(0);
      llvm::IRBuilder<> Builder(itp);

      // Compute alloca index: (operand - rsp_load) - min_offset
      // For constant offsets, InstCombine will fold sub(add(rsp,C), rsp) → C.
      // For variable offsets, sub(add(add(rsp,C),V), rsp) → C+V, which
      // then becomes (C+V) - min_offset = the correct alloca byte index.
      llvm::Value *rsp_relative = Builder.CreateSub(operand, base_load,
                                                     "rsp_rel");
      llvm::Value *alloca_idx;
      if (min_offset != 0) {
        alloca_idx = Builder.CreateAdd(
            rsp_relative,
            llvm::ConstantInt::get(i64_ty, -min_offset), "frame_idx");
      } else {
        alloca_idx = rsp_relative;
      }

      auto *gep = Builder.CreateGEP(i8_ty, frame_alloca, alloca_idx,
                                     "frame_ptr");

      itp->replaceAllUsesWith(gep);
      itp->eraseFromParent();
      changed = true;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
