#include "omill/Passes/VMHashElimination.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/BinaryMemoryMap.h"

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

llvm::Value *stripIntCasts(llvm::Value *V) {
  for (;;) {
    if (auto *Z = llvm::dyn_cast<llvm::ZExtInst>(V)) {
      V = Z->getOperand(0);
      continue;
    }
    if (auto *S = llvm::dyn_cast<llvm::SExtInst>(V)) {
      V = S->getOperand(0);
      continue;
    }
    if (auto *T = llvm::dyn_cast<llvm::TruncInst>(V)) {
      V = T->getOperand(0);
      continue;
    }
    break;
  }
  return V;
}

bool containsTaintedValue(llvm::Value *V,
                          const llvm::DenseSet<llvm::Instruction *> &tainted,
                          llvm::SmallPtrSetImpl<llvm::Value *> &visited,
                          unsigned depth = 0) {
  if (!V || depth > 24)
    return false;
  V = stripIntCasts(V);
  if (!visited.insert(V).second)
    return false;
  if (auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
    if (tainted.count(I))
      return true;
    if (auto *PHI = llvm::dyn_cast<llvm::PHINode>(I)) {
      for (unsigned i = 0; i < PHI->getNumIncomingValues(); ++i) {
        if (containsTaintedValue(PHI->getIncomingValue(i), tainted, visited,
                                 depth + 1))
          return true;
      }
      return false;
    }
    if (auto *Sel = llvm::dyn_cast<llvm::SelectInst>(I)) {
      return containsTaintedValue(Sel->getTrueValue(), tainted, visited,
                                  depth + 1) ||
             containsTaintedValue(Sel->getFalseValue(), tainted, visited,
                                  depth + 1);
    }
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(I)) {
      return containsTaintedValue(BO->getOperand(0), tainted, visited,
                                  depth + 1) ||
             containsTaintedValue(BO->getOperand(1), tainted, visited,
                                  depth + 1);
    }
  }
  return false;
}

bool matchAddConst(llvm::Value *V, llvm::Value *&X, uint64_t &C) {
  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(stripIntCasts(V));
  if (!BO || BO->getOpcode() != llvm::Instruction::Add)
    return false;
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
    if (CI->getBitWidth() > 64)
      return false;
    C = CI->getZExtValue();
    X = BO->getOperand(1);
    return true;
  }
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
    if (CI->getBitWidth() > 64)
      return false;
    C = CI->getZExtValue();
    X = BO->getOperand(0);
    return true;
  }
  return false;
}

bool matchSubConst(llvm::Value *V, llvm::Value *&X, uint64_t &C) {
  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(stripIntCasts(V));
  if (!BO || BO->getOpcode() != llvm::Instruction::Sub)
    return false;
  auto *CI = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
  if (!CI)
    return false;
  if (CI->getBitWidth() > 64)
    return false;
  C = CI->getZExtValue();
  X = BO->getOperand(0);
  return true;
}

bool matchLow32Expr(llvm::Value *V, llvm::Value *&Root) {
  V = stripIntCasts(V);
  // Form A: and i64 X, 0xFFFFFFFF
  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    if (BO->getOpcode() == llvm::Instruction::And) {
      auto *C0 = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0));
      auto *C1 = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
      if (C0 && C0->getBitWidth() <= 64 &&
          C0->getZExtValue() == 0xFFFFFFFFULL) {
        Root = BO->getOperand(1);
        return true;
      }
      if (C1 && C1->getBitWidth() <= 64 &&
          C1->getZExtValue() == 0xFFFFFFFFULL) {
        Root = BO->getOperand(0);
        return true;
      }
    }
  }
  // Form B: zext(trunc X to i32) to i64
  if (auto *Z = llvm::dyn_cast<llvm::ZExtInst>(V)) {
    if (auto *T = llvm::dyn_cast<llvm::TruncInst>(Z->getOperand(0))) {
      if (T->getType()->isIntegerTy(32)) {
        Root = T->getOperand(0);
        return true;
      }
    }
  }
  // Form C: trunc X to i32
  if (auto *T = llvm::dyn_cast<llvm::TruncInst>(V)) {
    if (T->getType()->isIntegerTy(32)) {
      Root = T->getOperand(0);
      return true;
    }
  }
  return false;
}

/// Canonicalization guards we want to eliminate:
///   (target - image_base) < image_size
///   (u32)target < image_size
///   (u32)(target - image_base) < image_size
///   (u32)(target - 0x40000000) < image_size
bool isCanonicalGuardCmp(llvm::ICmpInst *cmp, uint64_t image_base,
                         uint64_t image_size, llvm::Value *&target_expr) {
  target_expr = nullptr;
  if (!cmp || (cmp->getPredicate() != llvm::ICmpInst::ICMP_ULT &&
               cmp->getPredicate() != llvm::ICmpInst::ICMP_ULE))
    return false;

  auto *size_ci = llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(1));
  if (!size_ci)
    return false;
  if (size_ci->getBitWidth() > 64)
    return false;
  if (size_ci->getZExtValue() != image_size)
    return false;

  llvm::Value *lhs = cmp->getOperand(0);
  llvm::Value *root = nullptr;

  // (target - image_base) < image_size
  uint64_t sub_c = 0;
  if (matchSubConst(lhs, root, sub_c) && sub_c == image_base) {
    target_expr = root;
    return true;
  }

  // low32 forms.
  if (!matchLow32Expr(lhs, root))
    return false;

  target_expr = root;
  // (u32)target < image_size
  if (llvm::isa<llvm::Instruction>(stripIntCasts(root)) ||
      llvm::isa<llvm::Argument>(stripIntCasts(root)))
    return true;

  // (u32)(target - K) < image_size, K in {image_base, 0x40000000}
  llvm::Value *sub_x = nullptr;
  if (matchSubConst(root, sub_x, sub_c) &&
      (sub_c == image_base || sub_c == 0x40000000ULL)) {
    target_expr = sub_x;
    return true;
  }
  return false;
}

bool hasCanonicalSelectUse(llvm::ICmpInst *cmp, uint64_t image_base) {
  for (auto *U : cmp->users()) {
    auto *Sel = llvm::dyn_cast<llvm::SelectInst>(U);
    if (!Sel)
      continue;
    llvm::Value *X = nullptr;
    uint64_t C = 0;
    if (matchAddConst(Sel->getTrueValue(), X, C) && C == image_base)
      return true;
    if (matchAddConst(Sel->getFalseValue(), X, C) && C == image_base)
      return true;
  }
  return false;
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

  // Binary image info for canonical jump-target guard recognition.
  const BinaryMemoryMap *map = nullptr;
  uint64_t image_base = 0;
  uint64_t image_size = 0;
  {
    auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
    if (auto *Res =
            MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent())) {
      map = Res;
      image_base = map->imageBase();
      image_size = map->imageSize();
    }
  }

  bool changed = false;
  unsigned integrity_count = 0;
  unsigned range_count = 0;
  unsigned canonical_range_count = 0;

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
      uint64_t abs_val = 0;
      if (ci->getBitWidth() > 64) {
        abs_val = ~0ULL;
      } else {
        abs_val = ci->getValue().isNegative()
                      ? (uint64_t) (-ci->getSExtValue())
                      : ci->getZExtValue();
      }
      if (abs_val <= kIntegrityConstThreshold)
        continue;

      cmp->replaceAllUsesWith(
          llvm::ConstantInt::getTrue(cmp->getContext()));
      changed = true;
      ++integrity_count;
    }
  }

  // Step 4: Replace range checks.
  // Range-check sub-patterns in functions that have murmur rounds:
  //
  // 4a: icmp ugt/uge i64 %X, <const> where const > 2^48 → i1 true
  // 4b: call @llvm.umax.i64(%X, <const>) where const > 2^48
  //     → find downstream and(result, 1) → replace with i64 1
  // 4c: canonical jump-target guards (ult) fed by tainted murmur data:
  //       (target - image_base) < image_size
  //       (u32)target < image_size
  //       (u32)(target - image_base) < image_size
  //       (u32)(target - 0x40000000) < image_size
  //     when used by address-rebasing select chains.

  for (auto &BB : F) {
    for (auto &I : BB) {
      // 4a: icmp ugt/uge with large constant.
      if (auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        // 4c: canonical jump-target guard cleanup on tainted expressions.
        if (map && image_base != 0 && image_size != 0) {
          llvm::Value *target_expr = nullptr;
          if (isCanonicalGuardCmp(cmp, image_base, image_size, target_expr) &&
              hasCanonicalSelectUse(cmp, image_base)) {
            llvm::SmallPtrSet<llvm::Value *, 32> visited;
            if (containsTaintedValue(target_expr, tainted, visited)) {
              cmp->replaceAllUsesWith(
                  llvm::ConstantInt::getTrue(cmp->getContext()));
              changed = true;
              ++canonical_range_count;
              continue;
            }
          }
        }

        if (cmp->getPredicate() != llvm::ICmpInst::ICMP_UGT &&
            cmp->getPredicate() != llvm::ICmpInst::ICMP_UGE)
          continue;

        llvm::ConstantInt *ci = nullptr;
        if (auto *c = llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(1)))
          ci = c;
        else if (auto *c =
                     llvm::dyn_cast<llvm::ConstantInt>(cmp->getOperand(0)))
          ci = c;
        if (!ci)
          continue;
        if (ci->getBitWidth() <= 64 &&
            ci->getZExtValue() <= kRangeConstThreshold)
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
      if (!ci)
        continue;
      if (ci->getBitWidth() <= 64 &&
          ci->getZExtValue() <= kRangeConstThreshold)
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

  unsigned remaining_canonical_guards = 0;
  if (map && image_base != 0 && image_size != 0) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I);
        if (!cmp)
          continue;
        llvm::Value *target_expr = nullptr;
        if (!isCanonicalGuardCmp(cmp, image_base, image_size, target_expr))
          continue;
        if (!hasCanonicalSelectUse(cmp, image_base))
          continue;
        ++remaining_canonical_guards;
      }
    }
  }

  if (integrity_count > 0 || range_count > 0 || canonical_range_count > 0 ||
      remaining_canonical_guards > 0) {
    llvm::errs() << "VMHashElimination[" << F.getName()
                 << "]: eliminated " << integrity_count
                 << " integrity checks, " << range_count
                 << " range checks, " << canonical_range_count
                 << " canonical guards; remaining_canonical_guards="
                 << remaining_canonical_guards << " (" << anchors.size()
                 << " murmur rounds found)\n";
  }

  if (!changed)
    return llvm::PreservedAnalyses::all();
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
