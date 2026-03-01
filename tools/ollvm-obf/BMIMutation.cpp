#include "BMIMutation.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/IR/Module.h>

#include <random>
#include <vector>

namespace {

// ── Target feature checks ───────────────────────────────────────────

static bool hasBMI1(const llvm::Function &F) {
  if (!F.hasFnAttribute("target-features")) return false;
  return F.getFnAttribute("target-features").getValueAsString().contains("+bmi");
}

static bool hasBMI2(const llvm::Function &F) {
  if (!F.hasFnAttribute("target-features")) return false;
  return F.getFnAttribute("target-features").getValueAsString().contains("+bmi2");
}

// ── Intrinsic ID helpers ────────────────────────────────────────────

static llvm::Intrinsic::ID bextrID(llvm::Type *Ty) {
  return Ty->isIntegerTy(64) ? llvm::Intrinsic::x86_bmi_bextr_64
                              : llvm::Intrinsic::x86_bmi_bextr_32;
}

static llvm::Intrinsic::ID bzhiID(llvm::Type *Ty) {
  return Ty->isIntegerTy(64) ? llvm::Intrinsic::x86_bmi_bzhi_64
                              : llvm::Intrinsic::x86_bmi_bzhi_32;
}

static llvm::Intrinsic::ID pdepID(llvm::Type *Ty) {
  return Ty->isIntegerTy(64) ? llvm::Intrinsic::x86_bmi_pdep_64
                              : llvm::Intrinsic::x86_bmi_pdep_32;
}

static llvm::Intrinsic::ID pextID(llvm::Type *Ty) {
  return Ty->isIntegerTy(64) ? llvm::Intrinsic::x86_bmi_pext_64
                              : llvm::Intrinsic::x86_bmi_pext_32;
}

// ── Mask analysis ───────────────────────────────────────────────────

/// If \p mask is a contiguous run of set bits, return {start, length}.
/// Otherwise return {0, 0}.
static std::pair<unsigned, unsigned> contiguousBits(uint64_t mask,
                                                     unsigned bitWidth) {
  if (mask == 0) return {0, 0};
  unsigned start = llvm::countr_zero(mask);
  uint64_t shifted = mask >> start;
  unsigned len = llvm::countr_one(shifted);
  if (start + len > bitWidth) return {0, 0};
  // Verify no stray bits above the run.
  uint64_t expected = len < 64 ? ((uint64_t(1) << len) - 1) : ~uint64_t(0);
  if (shifted != expected) return {0, 0};
  return {start, len};
}

// ── Transform: XOR → ANDN pair ─────────────────────────────────────
// x ^ y  =  (~x & y) | (~y & x)
// Backend: ANDN + ANDN + OR

static llvm::Value *xorViaAndn(llvm::IRBuilder<> &B, llvm::Value *X,
                                llvm::Value *Y) {
  auto *AllOnes = llvm::ConstantInt::get(X->getType(), -1);
  auto *NotX = B.CreateXor(X, AllOnes);
  auto *T1   = B.CreateAnd(NotX, Y);   // ANDN(X, Y)
  auto *NotY = B.CreateXor(Y, AllOnes);
  auto *T2   = B.CreateAnd(NotY, X);   // ANDN(Y, X)
  return B.CreateOr(T1, T2);
}

// ── Transform: OR → De Morgan with ANDN ────────────────────────────
// x | y  =  ~(~x & ~y)
// Backend: NOT + ANDN + NOT   (ANDN pattern: and(xor(X,-1), notY))

static llvm::Value *orViaAndn(llvm::IRBuilder<> &B, llvm::Value *X,
                               llvm::Value *Y) {
  auto *AllOnes = llvm::ConstantInt::get(X->getType(), -1);
  auto *NotY    = B.CreateXor(Y, AllOnes);
  // ~X & ~Y  =  andn(X, ~Y)  → backend matches (and (xor X, -1), NotY)
  auto *NotX = B.CreateXor(X, AllOnes);
  auto *T    = B.CreateAnd(NotX, NotY);
  return B.CreateXor(T, AllOnes);
}

// ── Transform: AND → nested ANDN ───────────────────────────────────
// x & y  =  ~(~y & x) & x
// Backend: ANDN + ANDN

static llvm::Value *andViaAndn(llvm::IRBuilder<> &B, llvm::Value *X,
                                llvm::Value *Y) {
  auto *AllOnes = llvm::ConstantInt::get(X->getType(), -1);
  auto *NotY    = B.CreateXor(Y, AllOnes);
  auto *Inner   = B.CreateAnd(NotY, X);             // ANDN(Y, X)
  auto *NotInner = B.CreateXor(Inner, AllOnes);
  return B.CreateAnd(NotInner, X);                   // ANDN(Inner, X)
}

// ── Transform: AND constant (contiguous from bit 0) → BZHI ─────────

static llvm::Value *andConstToBzhi(llvm::IRBuilder<> &B, llvm::Value *X,
                                    unsigned width, llvm::Module &M) {
  auto *Fn = llvm::Intrinsic::getOrInsertDeclaration(&M, bzhiID(X->getType()));
  return B.CreateCall(Fn, {X, llvm::ConstantInt::get(X->getType(), width)});
}

// ── Transform: AND constant (contiguous at any position) → BEXTR ───

static llvm::Value *andConstToBextr(llvm::IRBuilder<> &B, llvm::Value *X,
                                     unsigned start, unsigned len,
                                     llvm::Module &M) {
  uint64_t ctrl = start | (uint64_t(len) << 8);
  auto *Fn = llvm::Intrinsic::getOrInsertDeclaration(&M, bextrID(X->getType()));
  auto *Extracted = B.CreateCall(
      Fn, {X, llvm::ConstantInt::get(X->getType(), ctrl)});
  if (start == 0) return Extracted;
  // BEXTR shifts the field down to bit 0 — shift back up to original position.
  return B.CreateShl(Extracted, start);
}

// ── Identity: x = blsi(x) | blsr(x) ────────────────────────────────
// blsi(x) = x & (-x)     — isolate lowest set bit
// blsr(x) = x & (x - 1)  — reset lowest set bit
// blsi(x) | blsr(x) = x  for all x (including 0)

static llvm::Value *identityBlsiBlsr(llvm::IRBuilder<> &B, llvm::Value *X,
                                      llvm::SmallPtrSetImpl<llvm::Value *> &created) {
  auto *Ty   = X->getType();
  auto *NegX = B.CreateNeg(X);
  auto *Blsi = B.CreateAnd(X, NegX);
  auto *DecX = B.CreateSub(X, llvm::ConstantInt::get(Ty, 1));
  auto *Blsr = B.CreateAnd(X, DecX);
  auto *Result = B.CreateOr(Blsi, Blsr);

  created.insert(NegX); created.insert(Blsi);
  created.insert(DecX); created.insert(Blsr);
  created.insert(Result);
  return Result;
}

// ── Identity: x = pdep(pext(x,M),M) | pdep(pext(x,~M),~M) ─────────
// For any mask M, splitting and reassembling preserves all bits.

static llvm::Value *identityPdepPext(llvm::IRBuilder<> &B, llvm::Value *X,
                                      uint64_t mask, llvm::Module &Mod,
                                      llvm::SmallPtrSetImpl<llvm::Value *> &created) {
  auto *Ty   = X->getType();
  unsigned bits = Ty->getIntegerBitWidth();
  uint64_t notMask = bits == 32 ? (~mask & 0xFFFFFFFFULL) : ~mask;

  auto *M    = llvm::ConstantInt::get(Ty, mask);
  auto *NotM = llvm::ConstantInt::get(Ty, notMask);

  auto *PextFn = llvm::Intrinsic::getOrInsertDeclaration(&Mod, pextID(Ty));
  auto *PdepFn = llvm::Intrinsic::getOrInsertDeclaration(&Mod, pdepID(Ty));

  auto *E1 = B.CreateCall(PextFn, {X, M});
  auto *D1 = B.CreateCall(PdepFn, {E1, M});
  auto *E2 = B.CreateCall(PextFn, {X, NotM});
  auto *D2 = B.CreateCall(PdepFn, {E2, NotM});
  auto *Result = B.CreateOr(D1, D2);

  created.insert(E1); created.insert(D1);
  created.insert(E2); created.insert(D2);
  created.insert(Result);
  return Result;
}

// ── Candidate collection ────────────────────────────────────────────

enum CandidateKind { CK_Xor, CK_Or, CK_And, CK_AndConst, CK_Identity };

struct Candidate {
  llvm::Instruction *inst;
  CandidateKind kind;
  unsigned maskStart = 0;
  unsigned maskLen   = 0;
};

}  // anonymous namespace

// ═════════════════════════════════════════════════════════════════════

bool ollvm::bmiMutateFunction(llvm::Function &F, uint32_t seed,
                               const ollvm::FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg)) return false;

  bool bmi1 = hasBMI1(F);
  bool bmi2 = hasBMI2(F);
  if (!bmi1 && !bmi2) return false;

  std::mt19937 rng(seed ^ std::hash<std::string>{}(F.getName().str()));
  llvm::Module &M = *F.getParent();

  // Collect candidates (snapshot — avoids iterator invalidation).
  std::vector<Candidate> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *Ty = I.getType();
      if (!Ty->isIntegerTy(32) && !Ty->isIntegerTy(64))
        continue;

      if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        switch (BO->getOpcode()) {
        case llvm::Instruction::Xor: {
          // Skip XOR-with-minus-one (that's NOT, an ANDN building block).
          if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1)))
            if (C->isMinusOne()) continue;
          if (bmi1)
            candidates.push_back({BO, CK_Xor});
          break;
        }
        case llvm::Instruction::Or:
          if (bmi1) candidates.push_back({BO, CK_Or});
          break;
        case llvm::Instruction::And: {
          if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
            unsigned bits = Ty->getIntegerBitWidth();
            auto [start, len] = contiguousBits(C->getZExtValue(), bits);
            if (len > 0 && len < bits && (bmi1 || bmi2)) {
              candidates.push_back({BO, CK_AndConst, start, len});
              continue;
            }
          }
          if (bmi1) candidates.push_back({BO, CK_And});
          break;
        }
        default:
          // Add, Sub, Mul, etc: eligible for identity wrapping.
          if (I.getNumUses() > 0)
            candidates.push_back({BO, CK_Identity});
          break;
        }
      } else if (!llvm::isa<llvm::PHINode>(&I) && !I.isTerminator() &&
                 I.getNumUses() > 0) {
        // Non-binary i32/i64 producers: eligible for identity wrapping.
        candidates.push_back({&I, CK_Identity});
      }
    }
  }

  if (candidates.empty()) return false;

  bool changed = false;

  for (auto &cand : candidates) {
    if (!shouldTransform(rng, cfg)) continue;

    auto *I = cand.inst;
    // Guard against instructions erased by an earlier iteration.
    if (I->getParent() == nullptr) continue;

    llvm::Value *replacement = nullptr;

    if (cand.kind != CK_Identity) {
      // Binary-op transforms: insert replacement at the same position.
      llvm::IRBuilder<> B(I);

      auto *BO = llvm::cast<llvm::BinaryOperator>(I);
      auto *LHS = BO->getOperand(0);
      auto *RHS = BO->getOperand(1);

      switch (cand.kind) {
      case CK_Xor:
        replacement = xorViaAndn(B, LHS, RHS);
        break;
      case CK_Or:
        replacement = orViaAndn(B, LHS, RHS);
        break;
      case CK_And:
        replacement = andViaAndn(B, LHS, RHS);
        break;
      case CK_AndConst:
        if (cand.maskStart == 0 && bmi2)
          replacement = andConstToBzhi(B, LHS, cand.maskLen, M);
        else if (bmi1)
          replacement = andConstToBextr(B, LHS, cand.maskStart, cand.maskLen, M);
        break;
      default:
        break;
      }

      if (replacement) {
        I->replaceAllUsesWith(replacement);
        I->eraseFromParent();
        changed = true;
      }
    } else {
      // Identity transform: insert after I, replace uses selectively.
      auto *next = I->getNextNonDebugInstruction();
      if (!next) continue;

      llvm::IRBuilder<> B(next);
      llvm::SmallPtrSet<llvm::Value *, 8> created;

      unsigned choice = std::uniform_int_distribution<unsigned>(0, bmi2 ? 1 : 0)(rng);

      if (choice == 0) {
        replacement = identityBlsiBlsr(B, I, created);
      } else {
        uint64_t mask = std::uniform_int_distribution<uint64_t>(
            1, I->getType()->isIntegerTy(32) ? 0xFFFFFFFEULL
                                              : ~uint64_t(1))(rng);
        replacement = identityPdepPext(B, I, mask, M, created);
      }

      if (replacement) {
        I->replaceUsesWithIf(replacement, [&](llvm::Use &U) {
          return !created.count(U.getUser());
        });
        changed = true;
      }
    }
  }

  return changed;
}

void ollvm::bmiMutateModule(llvm::Module &M, uint32_t seed,
                             const ollvm::FilterConfig &cfg) {
  for (auto &F : M)
    bmiMutateFunction(F, seed, cfg);
}
