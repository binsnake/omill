#include "omill/Passes/ExpandI128DivRem.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

namespace omill {
namespace {

/// Emit unsigned 128-bit division using a binary long-division loop.
/// Returns {quotient, remainder}.
std::pair<llvm::Value *, llvm::Value *>
emitUDivRem128(llvm::IRBuilder<> &B, llvm::Value *a, llvm::Value *b) {
  auto &Ctx = B.getContext();
  auto *i128 = llvm::Type::getInt128Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *zero128 = llvm::ConstantInt::get(i128, 0);
  auto *one128 = llvm::ConstantInt::get(i128, 1);
  auto *c64 = llvm::ConstantInt::get(i128, 64);
  auto *c127 = llvm::ConstantInt::get(i128, 127);

  // Fast path: if both operands fit in 64 bits, use i64 division.
  auto *a_hi = B.CreateTrunc(B.CreateLShr(a, c64), i64_ty, "a.hi");
  auto *b_hi = B.CreateTrunc(B.CreateLShr(b, c64), i64_ty, "b.hi");
  auto *zero64 = llvm::ConstantInt::get(i64_ty, 0);
  auto *both_fit = B.CreateAnd(B.CreateICmpEQ(a_hi, zero64),
                               B.CreateICmpEQ(b_hi, zero64), "both.fit64");

  auto *F = B.GetInsertBlock()->getParent();
  auto *entry_bb = B.GetInsertBlock();

  auto *fast_bb = llvm::BasicBlock::Create(Ctx, "udiv128.fast", F);
  auto *loop_pre = llvm::BasicBlock::Create(Ctx, "udiv128.pre", F);
  auto *loop_bb = llvm::BasicBlock::Create(Ctx, "udiv128.loop", F);
  auto *done_bb = llvm::BasicBlock::Create(Ctx, "udiv128.done", F);

  // Move all instructions after the current insert point into done_bb.
  // We need to split the block.
  auto *split_point = &*B.GetInsertPoint();
  done_bb->splice(done_bb->begin(), entry_bb, split_point->getIterator(),
                  entry_bb->end());

  // The old terminator is now in done_bb but successors' PHI nodes still
  // reference entry_bb.  Update them to reference done_bb instead.
  if (auto *term = done_bb->getTerminator()) {
    for (unsigned i = 0, e = term->getNumSuccessors(); i < e; ++i)
      term->getSuccessor(i)->replacePhiUsesWith(entry_bb, done_bb);
  }

  // Now entry_bb ends without a terminator — add the branch.
  B.SetInsertPoint(entry_bb);
  B.CreateCondBr(both_fit, fast_bb, loop_pre);

  // Fast path.
  B.SetInsertPoint(fast_bb);
  auto *a_lo = B.CreateTrunc(a, i64_ty, "a.lo");
  auto *b_lo = B.CreateTrunc(b, i64_ty, "b.lo");
  auto *q64 = B.CreateUDiv(a_lo, b_lo, "q64");
  auto *r64 = B.CreateURem(a_lo, b_lo, "r64");
  auto *q_fast = B.CreateZExt(q64, i128, "q.fast");
  auto *r_fast = B.CreateZExt(r64, i128, "r.fast");
  B.CreateBr(done_bb);

  // Loop preheader.
  B.SetInsertPoint(loop_pre);
  B.CreateBr(loop_bb);

  // Loop body: shift-and-subtract binary long division.
  B.SetInsertPoint(loop_bb);
  auto *i_phi = B.CreatePHI(i32_ty, 2, "i");
  auto *q_phi = B.CreatePHI(i128, 2, "q.loop");
  auto *r_phi = B.CreatePHI(i128, 2, "r.loop");

  auto *bit_idx = B.CreateZExt(i_phi, i128, "bit.idx");
  auto *shift = B.CreateSub(c127, bit_idx, "shift");
  auto *bit = B.CreateAnd(B.CreateLShr(a, shift), one128, "bit");
  auto *r_shifted = B.CreateOr(B.CreateShl(r_phi, one128), bit, "r.shift");

  auto *ge = B.CreateICmpUGE(r_shifted, b, "r.ge.b");
  auto *r_sub = B.CreateSub(r_shifted, b, "r.sub");
  auto *r_new = B.CreateSelect(ge, r_sub, r_shifted, "r.new");
  auto *q_bit = B.CreateShl(one128, shift, "q.bit");
  auto *q_new = B.CreateSelect(ge, B.CreateOr(q_phi, q_bit), q_phi, "q.new");

  auto *i_next = B.CreateAdd(i_phi, llvm::ConstantInt::get(i32_ty, 1), "i.next");
  auto *done = B.CreateICmpEQ(i_next, llvm::ConstantInt::get(i32_ty, 128), "loop.done");

  i_phi->addIncoming(llvm::ConstantInt::get(i32_ty, 0), loop_pre);
  i_phi->addIncoming(i_next, loop_bb);
  q_phi->addIncoming(zero128, loop_pre);
  q_phi->addIncoming(q_new, loop_bb);
  r_phi->addIncoming(zero128, loop_pre);
  r_phi->addIncoming(r_new, loop_bb);

  B.CreateCondBr(done, done_bb, loop_bb);

  // Merge results in done_bb.
  B.SetInsertPoint(done_bb, done_bb->begin());
  auto *q_final = B.CreatePHI(i128, 2, "q.final");
  q_final->addIncoming(q_fast, fast_bb);
  q_final->addIncoming(q_new, loop_bb);
  auto *r_final = B.CreatePHI(i128, 2, "r.final");
  r_final->addIncoming(r_fast, fast_bb);
  r_final->addIncoming(r_new, loop_bb);

  return {q_final, r_final};
}

}  // namespace

llvm::PreservedAnalyses ExpandI128DivRemPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  // Collect i128 sdiv/udiv/srem/urem instructions.
  llvm::SmallVector<llvm::BinaryOperator *, 4> worklist;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!BO || !BO->getType()->isIntegerTy(128))
        continue;
      switch (BO->getOpcode()) {
      case llvm::Instruction::SDiv:
      case llvm::Instruction::UDiv:
      case llvm::Instruction::SRem:
      case llvm::Instruction::URem:
        worklist.push_back(BO);
        break;
      default:
        break;
      }
    }
  }

  if (worklist.empty())
    return llvm::PreservedAnalyses::all();

  auto *i128 = llvm::Type::getInt128Ty(F.getContext());

  for (auto *BO : worklist) {
    llvm::IRBuilder<> B(BO);
    auto *lhs = BO->getOperand(0);
    auto *rhs = BO->getOperand(1);

    bool is_signed = (BO->getOpcode() == llvm::Instruction::SDiv ||
                      BO->getOpcode() == llvm::Instruction::SRem);
    bool is_div = (BO->getOpcode() == llvm::Instruction::SDiv ||
                   BO->getOpcode() == llvm::Instruction::UDiv);

    llvm::Value *a = lhs, *b = rhs;
    llvm::Value *a_sign = nullptr, *b_sign = nullptr;

    if (is_signed) {
      auto *c127 = llvm::ConstantInt::get(i128, 127);
      a_sign = B.CreateAShr(a, c127, "a.sign");
      b_sign = B.CreateAShr(b, c127, "b.sign");
      a = B.CreateSub(B.CreateXor(a, a_sign), a_sign, "a.abs");
      b = B.CreateSub(B.CreateXor(b, b_sign), b_sign, "b.abs");
    }

    auto [q, r] = emitUDivRem128(B, a, b);

    llvm::Value *result;
    if (is_div) {
      if (is_signed) {
        auto *q_sign = B.CreateXor(a_sign, b_sign, "q.sign");
        result = B.CreateSub(B.CreateXor(q, q_sign), q_sign, "sdiv128");
      } else {
        result = q;
      }
    } else {
      if (is_signed) {
        result = B.CreateSub(B.CreateXor(r, a_sign), a_sign, "srem128");
      } else {
        result = r;
      }
    }

    BO->replaceAllUsesWith(result);
    BO->eraseFromParent();
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
