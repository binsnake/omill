#include "omill/Passes/VMHashElimination.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/raw_ostream.h>

using namespace llvm::PatternMatch;

namespace omill {

namespace {

// Threshold constants.
constexpr uint64_t kIntegrityConstThreshold = 1ULL << 32;
constexpr uint64_t kRangeConstThreshold = 1ULL << 48;

/// Step 1: Find murmur anchors.
/// A `mul` instruction M is a murmur mul if it has both lshr(M, 60) and
/// lshr(M, 32) among its users.
llvm::SmallVector<llvm::Instruction *, 16>
findMurmurAnchors(llvm::Function &F) {
  llvm::SmallVector<llvm::Instruction *, 16> anchors;

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (I.getOpcode() != llvm::Instruction::Mul)
        continue;
      if (!I.getType()->isIntegerTy(64))
        continue;

      bool has_shift32 = false;
      bool has_shift60 = false;

      for (auto *user : I.users()) {
        auto *u_inst = llvm::dyn_cast<llvm::Instruction>(user);
        if (!u_inst)
          continue;
        if (match(u_inst, m_LShr(m_Specific(&I), m_SpecificInt(32))))
          has_shift32 = true;
        if (match(u_inst, m_LShr(m_Specific(&I), m_SpecificInt(60))))
          has_shift60 = true;
        if (has_shift32 && has_shift60)
          break;
      }

      if (has_shift32 && has_shift60)
        anchors.push_back(&I);
    }
  }

  return anchors;
}

/// Step 2: Forward taint BFS from murmur muls.
/// Propagates through arithmetic, shifts, casts, phi, select (value only).
/// Stops at load, store, call, icmp, br, switch, ret.
void taintBFS(const llvm::SmallVectorImpl<llvm::Instruction *> &seeds,
              llvm::DenseSet<llvm::Instruction *> &tainted) {
  llvm::SmallVector<llvm::Instruction *, 64> worklist;

  for (auto *seed : seeds) {
    if (tainted.insert(seed).second)
      worklist.push_back(seed);
  }

  while (!worklist.empty()) {
    auto *inst = worklist.pop_back_val();

    for (auto *user : inst->users()) {
      auto *u_inst = llvm::dyn_cast<llvm::Instruction>(user);
      if (!u_inst)
        continue;

      // Already tainted.
      if (tainted.count(u_inst))
        continue;

      bool propagate = false;

      switch (u_inst->getOpcode()) {
        // Binary arithmetic — always propagate.
        case llvm::Instruction::Xor:
        case llvm::Instruction::Or:
        case llvm::Instruction::And:
        case llvm::Instruction::Add:
        case llvm::Instruction::Sub:
          propagate = true;
          break;

        // Mul — only if one operand is tainted or constant.
        case llvm::Instruction::Mul: {
          auto *op0 = u_inst->getOperand(0);
          auto *op1 = u_inst->getOperand(1);
          bool op0_tainted =
              tainted.count(llvm::dyn_cast<llvm::Instruction>(op0));
          bool op1_tainted =
              tainted.count(llvm::dyn_cast<llvm::Instruction>(op1));
          bool op0_const = llvm::isa<llvm::ConstantInt>(op0);
          bool op1_const = llvm::isa<llvm::ConstantInt>(op1);
          propagate = op0_tainted || op1_tainted || op0_const || op1_const;
          break;
        }

        // Shifts.
        case llvm::Instruction::LShr:
        case llvm::Instruction::Shl:
        case llvm::Instruction::AShr:
          propagate = true;
          break;

        // Casts.
        case llvm::Instruction::Trunc:
        case llvm::Instruction::ZExt:
        case llvm::Instruction::SExt:
          propagate = true;
          break;

        // PHI — taint if any incoming is tainted.
        case llvm::Instruction::PHI:
          propagate = true;
          break;

        // Select — taint if a value operand (not condition) is tainted.
        case llvm::Instruction::Select: {
          auto *sel = llvm::cast<llvm::SelectInst>(u_inst);
          auto *tv = sel->getTrueValue();
          auto *fv = sel->getFalseValue();
          auto *tv_inst = llvm::dyn_cast<llvm::Instruction>(tv);
          auto *fv_inst = llvm::dyn_cast<llvm::Instruction>(fv);
          propagate =
              (tv_inst && tainted.count(tv_inst)) ||
              (fv_inst && tainted.count(fv_inst));
          break;
        }

        // Stop: load, store, call, icmp, br, switch, ret, etc.
        default:
          propagate = false;
          break;
      }

      if (propagate) {
        tainted.insert(u_inst);
        worklist.push_back(u_inst);
      }
    }
  }
}

}  // namespace

llvm::PreservedAnalyses VMHashEliminationPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  // Step 1: Find murmur anchors.
  auto anchors = findMurmurAnchors(F);
  if (anchors.empty())
    return llvm::PreservedAnalyses::all();

  // Step 2: Forward taint BFS.
  llvm::DenseSet<llvm::Instruction *> tainted;
  taintBFS(anchors, tainted);

  bool changed = false;
  unsigned integrity_count = 0;
  unsigned range_count = 0;

  // Step 3: Replace integrity checks.
  // icmp eq i64 %tainted, <large_const> → i1 true
  for (auto *inst : tainted) {
    for (auto *user : inst->users()) {
      auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(user);
      if (!cmp || cmp->getPredicate() != llvm::ICmpInst::ICMP_EQ)
        continue;
      if (!cmp->getType()->isIntegerTy(1))
        continue;

      // Find the constant operand.
      llvm::ConstantInt *ci = nullptr;
      if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(0)))
        ci = c;
      else if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(1)))
        ci = c;
      if (!ci)
        continue;

      // |const| > 2^32 threshold.
      uint64_t abs_val = ci->getValue().isNegative()
                             ? (uint64_t) (-ci->getSExtValue())
                             : ci->getZExtValue();
      if (abs_val <= kIntegrityConstThreshold)
        continue;

      cmp->replaceAllUsesWith(
          llvm::ConstantInt::getTrue(cmp->getContext()));
      changed = true;
      ++integrity_count;
    }
  }

  // Step 4: Replace range checks.
  // Two sub-patterns in functions that have murmur rounds:
  //
  // 4a: icmp ugt/uge i64 %X, <const> where const > 2^48 → i1 true
  // 4b: call @llvm.umax.i64(%X, <const>) where const > 2^48
  //     → find downstream and(result, 1) → replace with i64 1

  for (auto &BB : F) {
    for (auto &I : BB) {
      // 4a: icmp ugt/uge with large constant.
      if (auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        if (cmp->getPredicate() != llvm::ICmpInst::ICMP_UGT &&
            cmp->getPredicate() != llvm::ICmpInst::ICMP_UGE)
          continue;

        llvm::ConstantInt *ci = nullptr;
        if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(1)))
          ci = c;
        else if (auto *c =
                     llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(0)))
          ci = c;
        if (!ci || ci->getZExtValue() <= kRangeConstThreshold)
          continue;

        cmp->replaceAllUsesWith(
            llvm::ConstantInt::getTrue(cmp->getContext()));
        changed = true;
        ++range_count;
        continue;
      }

      // 4b: call @llvm.umax.i64 with large constant.
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->getIntrinsicID() != llvm::Intrinsic::umax)
        continue;
      if (!call->getType()->isIntegerTy(64))
        continue;

      // Check if one argument is a large constant.
      llvm::ConstantInt *ci = nullptr;
      if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(0)))
        ci = c;
      else if (auto *c =
                   llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1)))
        ci = c;
      if (!ci || ci->getZExtValue() <= kRangeConstThreshold)
        continue;

      // Find downstream and(result, 1) patterns.
      for (auto *user : call->users()) {
        auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(user);
        if (!bin || bin->getOpcode() != llvm::Instruction::And)
          continue;
        llvm::ConstantInt *and_const = nullptr;
        if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(bin->getOperand(0)))
          and_const = c;
        else if (auto *c =
                     llvm::dyn_cast<llvm::ConstantInt>(bin->getOperand(1)))
          and_const = c;
        if (!and_const || !and_const->isOne())
          continue;

        bin->replaceAllUsesWith(
            llvm::ConstantInt::get(bin->getType(), 1));
        changed = true;
        ++range_count;
      }
    }
  }

  if (integrity_count > 0 || range_count > 0) {
    llvm::errs() << "VMHashElimination[" << F.getName()
                 << "]: eliminated " << integrity_count
                 << " integrity checks, " << range_count
                 << " range checks (" << anchors.size()
                 << " murmur rounds found)\n";
  }

  if (!changed)
    return llvm::PreservedAnalyses::all();
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
