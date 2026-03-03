#include "omill/Passes/RecoverAllocaPointers.h"
#include "omill/Analysis/BinaryMemoryMap.h"

#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Support/raw_ostream.h>

static bool debugRecover() {
  static const bool enabled = [] {
    auto *e = std::getenv("OMILL_DEBUG_RECOVER_ALLOCA");
    return e && e[0] == '1';
  }();
  return enabled;
}

using namespace llvm;

namespace {

struct AllocaOffset {
  AllocaInst *AI;
  int64_t Offset;
};

/// Map from {AllocaInst*, byte_offset} to the unique stored i64 value.
/// Only populated for stores to GEP(alloca, constant_offset) with exactly
/// one store to that slot.
using StoreMap = DenseMap<std::pair<AllocaInst *, int64_t>, Value *>;

/// Speculative store map: tracks stores of any integer type.
/// Key = {AllocaInst*, byte_offset}, Value = vector of {stored Value*, bit width, StoreInst*}.
/// Multiple stores to the same slot are kept — resolved by program order at load time.
struct SpecStoreEntry {
  Value *Val;
  unsigned BitWidth;
  StoreInst *SI;
};
using SpecStoreMap = DenseMap<std::pair<AllocaInst *, int64_t>,
                             SmallVector<SpecStoreEntry, 2>>;

/// Try to decompose a GEP to {alloca, byte_offset}.
static std::optional<AllocaOffset> decomposeGEP(Value *Ptr,
                                                 const DataLayout &DL) {
  if (auto *AI = dyn_cast<AllocaInst>(Ptr))
    return AllocaOffset{AI, 0};
  if (auto *GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
    if (auto *AI = dyn_cast<AllocaInst>(GEP->getPointerOperand())) {
      APInt Off(64, 0);
      if (GEP->accumulateConstantOffset(DL, Off))
        return AllocaOffset{AI, Off.getSExtValue()};
    }
  }
  return std::nullopt;
}

/// Build a map of unique i64 stores: {alloca, offset} -> stored value.
static StoreMap buildStoreMap(Function &F, const DataLayout &DL) {
  StoreMap Map;
  DenseSet<std::pair<AllocaInst *, int64_t>> Ambiguous;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *SI = dyn_cast<StoreInst>(&I);
      if (!SI || !SI->getValueOperand()->getType()->isIntegerTy(64))
        continue;
      auto Decomp = decomposeGEP(SI->getPointerOperand(), DL);
      if (!Decomp)
        continue;
      auto Key = std::make_pair(Decomp->AI, Decomp->Offset);
      if (Ambiguous.count(Key))
        continue;
      auto [It, Inserted] = Map.try_emplace(Key, SI->getValueOperand());
      if (!Inserted) {
        Map.erase(It);
        Ambiguous.insert(Key);
      }
    }
  }
  return Map;
}

/// Build a general store map tracking all integer type stores.
static SpecStoreMap buildSpecStoreMap(Function &F, const DataLayout &DL) {
  SpecStoreMap Map;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *SI = dyn_cast<StoreInst>(&I);
      if (!SI)
        continue;
      auto *ValTy = SI->getValueOperand()->getType();
      if (!ValTy->isIntegerTy())
        continue;
      unsigned BW = ValTy->getIntegerBitWidth();
      auto Decomp = decomposeGEP(SI->getPointerOperand(), DL);
      if (!Decomp)
        continue;
      auto Key = std::make_pair(Decomp->AI, Decomp->Offset);
      Map[Key].push_back({SI->getValueOperand(), BW, SI});
    }
  }
  return Map;
}

/// Walk an integer value backward through add/sub with constant operands
/// looking for a ptrtoint(GEP alloca, C) root.  Also follows loads from
/// alloca slots if the StoreMap has a unique stored value for that slot.
/// Returns the alloca and accumulated constant offset if found.
static std::optional<AllocaOffset>
resolveToAlloca(Value *V, const DataLayout &DL,
                const StoreMap &Stores,
                SmallPtrSetImpl<Value *> &Visited) {
  if (!Visited.insert(V).second)
    return std::nullopt;

  // Base case: ptrtoint of alloca or GEP-into-alloca.
  if (auto *P2I = dyn_cast<PtrToIntInst>(V)) {
    Value *Ptr = P2I->getOperand(0);
    if (auto *AI = dyn_cast<AllocaInst>(Ptr))
      return AllocaOffset{AI, 0};
    if (auto *GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
      if (auto *AI = dyn_cast<AllocaInst>(GEP->getPointerOperand())) {
        APInt Off(64, 0);
        if (GEP->accumulateConstantOffset(DL, Off))
          return AllocaOffset{AI, Off.getSExtValue()};
      }
    }
    return std::nullopt;
  }

  // Follow loads through the store map.
  if (auto *LI = dyn_cast<LoadInst>(V)) {
    if (!LI->getType()->isIntegerTy(64))
      return std::nullopt;
    auto Decomp = decomposeGEP(LI->getPointerOperand(), DL);
    if (!Decomp)
      return std::nullopt;
    auto Key = std::make_pair(Decomp->AI, Decomp->Offset);
    auto It = Stores.find(Key);
    if (It == Stores.end())
      return std::nullopt;
    return resolveToAlloca(It->second, DL, Stores, Visited);
  }

  // Recurse through add(V, C), add(C, V), sub(V, C).
  if (auto *BO = dyn_cast<BinaryOperator>(V)) {
    if (BO->getOpcode() == Instruction::Add) {
      for (unsigned i = 0; i < 2; ++i) {
        if (auto *C = dyn_cast<ConstantInt>(BO->getOperand(i))) {
          if (auto Base =
                  resolveToAlloca(BO->getOperand(1 - i), DL, Stores, Visited))
            return AllocaOffset{Base->AI, Base->Offset + C->getSExtValue()};
        }
      }
    }
    if (BO->getOpcode() == Instruction::Sub) {
      if (auto *C = dyn_cast<ConstantInt>(BO->getOperand(1))) {
        if (auto Base =
                resolveToAlloca(BO->getOperand(0), DL, Stores, Visited))
          return AllocaOffset{Base->AI, Base->Offset - C->getSExtValue()};
      }
    }
  }

  return std::nullopt;
}

// ============================================================
// Speculative Concrete Evaluation
// ============================================================

/// Find an AllocaInst referenced by ptrtoint in the expression tree.
/// Follows loads through the spec store map to find alloca references.
static AllocaInst *findAllocaInExpr(Value *V,
                                     const SpecStoreMap &SSM,
                                     const DataLayout &DL,
                                     SmallPtrSetImpl<Value *> &Visited) {
  if (!Visited.insert(V).second)
    return nullptr;

  if (auto *P2I = dyn_cast<PtrToIntInst>(V)) {
    Value *Ptr = P2I->getOperand(0);
    if (auto *AI = dyn_cast<AllocaInst>(Ptr))
      return AI;
    if (auto *GEP = dyn_cast<GetElementPtrInst>(Ptr))
      if (auto *AI = dyn_cast<AllocaInst>(GEP->getPointerOperand()))
        return AI;
    return nullptr;
  }

  if (auto *BO = dyn_cast<BinaryOperator>(V)) {
    if (auto *AI = findAllocaInExpr(BO->getOperand(0), SSM, DL, Visited))
      return AI;
    return findAllocaInExpr(BO->getOperand(1), SSM, DL, Visited);
  }
  if (auto *CI = dyn_cast<CastInst>(V))
    return findAllocaInExpr(CI->getOperand(0), SSM, DL, Visited);
  if (auto *SI = dyn_cast<SelectInst>(V)) {
    if (auto *AI = findAllocaInExpr(SI->getTrueValue(), SSM, DL, Visited))
      return AI;
    if (auto *AI = findAllocaInExpr(SI->getFalseValue(), SSM, DL, Visited))
      return AI;
    return findAllocaInExpr(SI->getCondition(), SSM, DL, Visited);
  }
  if (auto *IC = dyn_cast<ICmpInst>(V)) {
    if (auto *AI = findAllocaInExpr(IC->getOperand(0), SSM, DL, Visited))
      return AI;
    return findAllocaInExpr(IC->getOperand(1), SSM, DL, Visited);
  }
  // Follow loads through spec store map to find alloca references.
  if (auto *LI = dyn_cast<LoadInst>(V)) {
    if (LI->getType()->isIntegerTy()) {
      auto Decomp = decomposeGEP(LI->getPointerOperand(), DL);
      if (Decomp) {
        // The load is from an alloca slot — the alloca itself is a candidate.
        // Also follow the stored value to find deeper alloca references.
        auto Key = std::make_pair(Decomp->AI, Decomp->Offset);
        auto SIt = SSM.find(Key);
        if (SIt != SSM.end()) {
          for (auto &E : SIt->second)
            if (auto *AI = findAllocaInExpr(E.Val, SSM, DL, Visited))
              return AI;
        }
        // The load address itself references an alloca.
        return Decomp->AI;
      }
    }
    return nullptr;
  }

  return nullptr;
}

/// Advance a simple xorshift64 PRNG and return the new state.
static uint64_t xorshift64(uint64_t &S) {
  S ^= S << 13;
  S ^= S >> 7;
  S ^= S << 17;
  return S;
}

/// Concrete evaluation of an integer expression tree.
/// Env maps Value* -> concrete uint64_t (pre-populated for alloca bases,
/// and populated on-the-fly with random values for unknown leaves).
/// SpecStoreMap enables following loads through stores of any integer type.
/// Returns nullopt only for genuinely unevaluable nodes (FP, vectors, etc.).
static std::optional<uint64_t>
concreteEval(Value *V,
             DenseMap<Value *, uint64_t> &Env,
             const SpecStoreMap &SSM,
             const DataLayout &DL,
             SmallPtrSetImpl<Value *> &InProgress,
             uint64_t &RNG) {
  // Cached result.
  auto CIt = Env.find(V);
  if (CIt != Env.end())
    return CIt->second;

  // Cycle detection.
  if (!InProgress.insert(V).second)
    return std::nullopt;

  std::optional<uint64_t> Result;

  if (auto *CI = dyn_cast<ConstantInt>(V)) {
    Result = CI->getZExtValue();

  } else if (isa<UndefValue>(V) || isa<PoisonValue>(V)) {
    Result = uint64_t(0);

  } else if (auto *P2I = dyn_cast<PtrToIntInst>(V)) {
    Value *Ptr = P2I->getOperand(0);
    if (auto *AI = dyn_cast<AllocaInst>(Ptr)) {
      auto It = Env.find(AI);
      if (It != Env.end()) Result = It->second;
    } else if (auto *GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
      if (auto *AI = dyn_cast<AllocaInst>(GEP->getPointerOperand())) {
        auto It = Env.find(AI);
        if (It != Env.end()) {
          APInt Off(64, 0);
          if (GEP->accumulateConstantOffset(DL, Off))
            Result = It->second + Off.getZExtValue();
        }
      }
    }

  } else if (auto *LI = dyn_cast<LoadInst>(V)) {
    if (LI->getType()->isIntegerTy()) {
      unsigned LoadBW = LI->getType()->getIntegerBitWidth();
      auto Decomp = decomposeGEP(LI->getPointerOperand(), DL);
      if (Decomp) {
        auto Key = std::make_pair(Decomp->AI, Decomp->Offset);
        auto SIt = SSM.find(Key);
        if (SIt != SSM.end()) {
          // Find the latest store BEFORE this load in program order.
          // Entries are in insertion order (instruction iteration order).
          Value *BestVal = nullptr;
          for (auto &E : SIt->second) {
            if (E.BitWidth != LoadBW)
              continue;
            // Same basic block: use comesBefore for precise ordering.
            if (E.SI->getParent() == LI->getParent()) {
              if (E.SI->comesBefore(LI))
                BestVal = E.Val;
            } else {
              // Cross-block: accept if the store dominates (conservative:
              // accept all, last one wins — Monte Carlo will validate).
              BestVal = E.Val;
            }
          }
          if (BestVal)
            Result = concreteEval(BestVal, Env, SSM, DL, InProgress, RNG);
        }
      }
    }
    // If not resolved through store map, treat as free variable below.

  } else if (auto *BO = dyn_cast<BinaryOperator>(V)) {
    auto L = concreteEval(BO->getOperand(0), Env, SSM, DL, InProgress, RNG);
    auto R = concreteEval(BO->getOperand(1), Env, SSM, DL, InProgress, RNG);
    if (L && R) {
      switch (BO->getOpcode()) {
      case Instruction::Add:  Result = *L + *R; break;
      case Instruction::Sub:  Result = *L - *R; break;
      case Instruction::Mul:  Result = *L * *R; break;
      case Instruction::Xor:  Result = *L ^ *R; break;
      case Instruction::And:  Result = *L & *R; break;
      case Instruction::Or:   Result = *L | *R; break;
      case Instruction::Shl:  Result = *L << (*R & 63); break;
      case Instruction::LShr: Result = *L >> (*R & 63); break;
      case Instruction::AShr:
        Result = (uint64_t)((int64_t)*L >> (*R & 63)); break;
      case Instruction::URem:
        Result = *R ? std::optional(*L % *R) : std::nullopt; break;
      case Instruction::UDiv:
        Result = *R ? std::optional(*L / *R) : std::nullopt; break;
      case Instruction::SDiv:
        if (*R && !((int64_t)*L == INT64_MIN && (int64_t)*R == -1))
          Result = (uint64_t)((int64_t)*L / (int64_t)*R);
        break;
      case Instruction::SRem:
        if (*R && !((int64_t)*L == INT64_MIN && (int64_t)*R == -1))
          Result = (uint64_t)((int64_t)*L % (int64_t)*R);
        break;
      default: break; // unsupported op
      }
    }

  } else if (auto *CI = dyn_cast<CastInst>(V)) {
    auto Op = concreteEval(CI->getOperand(0), Env, SSM, DL, InProgress, RNG);
    if (Op) {
      unsigned SrcBits = CI->getSrcTy()->getScalarSizeInBits();
      unsigned DstBits = CI->getDestTy()->getScalarSizeInBits();
      switch (CI->getOpcode()) {
      case Instruction::ZExt:
        Result = (SrcBits < 64) ? (*Op & ((1ULL << SrcBits) - 1)) : *Op;
        break;
      case Instruction::SExt: {
        uint64_t v = *Op;
        if (SrcBits < 64) {
          v &= (1ULL << SrcBits) - 1;
          if (v & (1ULL << (SrcBits - 1)))
            v |= ~((1ULL << SrcBits) - 1);
        }
        Result = v;
        break;
      }
      case Instruction::Trunc:
        Result = (DstBits < 64) ? (*Op & ((1ULL << DstBits) - 1)) : *Op;
        break;
      case Instruction::BitCast:
      case Instruction::PtrToInt:
      case Instruction::IntToPtr:
        Result = *Op;
        break;
      default: break; // unsupported cast
      }
    }

  } else if (auto *IC = dyn_cast<ICmpInst>(V)) {
    auto L = concreteEval(IC->getOperand(0), Env, SSM, DL, InProgress, RNG);
    auto R = concreteEval(IC->getOperand(1), Env, SSM, DL, InProgress, RNG);
    if (L && R) {
      bool Res;
      switch (IC->getPredicate()) {
      case ICmpInst::ICMP_EQ:  Res = *L == *R; break;
      case ICmpInst::ICMP_NE:  Res = *L != *R; break;
      case ICmpInst::ICMP_UGT: Res = *L > *R; break;
      case ICmpInst::ICMP_UGE: Res = *L >= *R; break;
      case ICmpInst::ICMP_ULT: Res = *L < *R; break;
      case ICmpInst::ICMP_ULE: Res = *L <= *R; break;
      case ICmpInst::ICMP_SGT: Res = (int64_t)*L > (int64_t)*R; break;
      case ICmpInst::ICMP_SGE: Res = (int64_t)*L >= (int64_t)*R; break;
      case ICmpInst::ICMP_SLT: Res = (int64_t)*L < (int64_t)*R; break;
      case ICmpInst::ICMP_SLE: Res = (int64_t)*L <= (int64_t)*R; break;
      default: goto done; // unsupported predicate
      }
      Result = Res ? 1ULL : 0ULL;
    }

  } else if (auto *SI = dyn_cast<SelectInst>(V)) {
    auto Cond = concreteEval(SI->getCondition(), Env, SSM, DL, InProgress, RNG);
    if (Cond)
      Result = (*Cond & 1)
        ? concreteEval(SI->getTrueValue(), Env, SSM, DL, InProgress, RNG)
        : concreteEval(SI->getFalseValue(), Env, SSM, DL, InProgress, RNG);
  }

done:
  InProgress.erase(V);

  // If we couldn't compute a result through known operations, and this is
  // a leaf-like value (argument, phi, call, unresolved load), assign a
  // random concrete value.  This enables testing whether the expression
  // is independent of these unknowns.
  if (!Result) {
    if (isa<Argument>(V) || isa<PHINode>(V) || isa<CallBase>(V) ||
        isa<LoadInst>(V)) {
      Result = xorshift64(RNG);
    } else {
      return std::nullopt; // genuinely unevaluable
    }
  }

  Env[V] = *Result;
  return *Result;
}

/// Try to speculatively resolve an inttoptr operand to a constant alloca
/// offset via Monte Carlo concrete evaluation.
/// Runs multiple trials with different random values for free variables.
/// Returns {alloca, offset} if the expression consistently evaluates to
/// alloca_base + constant_offset, independent of free variable values.
static std::optional<AllocaOffset>
trySpeculativeResolve(Value *V, AllocaInst *AI,
                      const SpecStoreMap &SSM,
                      const DataLayout &DL) {
  // Use a large aligned value that won't accidentally cancel out.
  constexpr uint64_t AllocaBase = 0x7FFE'0000'0000ULL;
  constexpr unsigned NumTrials = 16;

  // Collect ALL allocas in the function and assign them stable base addresses.
  // This is critical: expression trees may cross multiple allocas (e.g., outer
  // native_stack and inner native_stack.i after VM handler inlining).
  Function *Fn = AI->getFunction();
  SmallVector<AllocaInst *, 4> AllAllocas;
  for (auto &BB : *Fn)
    for (auto &I : BB)
      if (auto *A = dyn_cast<AllocaInst>(&I))
        AllAllocas.push_back(A);

  auto populateEnv = [&](DenseMap<Value *, uint64_t> &Env,
                         uint64_t TargetBase) {
    // Assign target alloca the varying base; others get fixed distinct bases.
    uint64_t OtherBase = 0x7FF0'0000'0000ULL;
    for (auto *A : AllAllocas) {
      if (A == AI)
        Env[A] = TargetBase;
      else {
        Env[A] = OtherBase;
        OtherBase -= 0x0001'0000'0000ULL; // 4GB separation
      }
    }
  };

  SmallVector<int64_t, 16> Offsets;
  SmallDenseSet<int64_t, 4> DistinctOffsets;

  for (unsigned Trial = 0; Trial < NumTrials; ++Trial) {
    DenseMap<Value *, uint64_t> Env;
    populateEnv(Env, AllocaBase);

    // Each trial uses a different RNG seed so free variables get
    // different concrete values.
    uint64_t RNG = 0xDEADBEEF12345678ULL ^
                   (uint64_t(Trial) * 0x9E3779B97F4A7C15ULL);

    SmallPtrSet<Value *, 32> InProgress;
    auto Result = concreteEval(V, Env, SSM, DL, InProgress, RNG);
    if (!Result)
      return std::nullopt;

    int64_t Offset = (int64_t)(*Result - AllocaBase);
    Offsets.push_back(Offset);
    DistinctOffsets.insert(Offset);
  }

  if (debugRecover())
    llvm::errs() << "    distinct offsets: " << DistinctOffsets.size()
                 << " / " << NumTrials << " trials\n";

  // If all trials give the same offset, it's constant.
  if (DistinctOffsets.size() != 1)
    return std::nullopt;

  // Cross-check: use a different alloca base with the same RNG seed as
  // trial 0 to confirm the expression is truly alloca-relative (the
  // coefficient of alloca_base in the expression is 1, not 0 or 2).
  constexpr uint64_t AllocaBase2 = 0x7FFF'0000'0000ULL;
  {
    DenseMap<Value *, uint64_t> Env;
    populateEnv(Env, AllocaBase2);
    uint64_t RNG = 0xDEADBEEF12345678ULL; // same seed as trial 0
    SmallPtrSet<Value *, 32> InProgress;
    auto Result = concreteEval(V, Env, SSM, DL, InProgress, RNG);
    if (!Result)
      return std::nullopt;
    int64_t Offset2 = (int64_t)(*Result - AllocaBase2);
    if (Offset2 != Offsets[0])
      return std::nullopt; // alloca base coefficient is not 1
  }

  return AllocaOffset{AI, Offsets[0]};
}

/// Try to resolve an inttoptr operand to a constant (non-alloca-relative)
/// value via Monte Carlo concrete evaluation. Returns the constant if the
/// expression consistently evaluates to a small set of values (1 or 2)
/// that are valid code addresses in the binary.
///
/// The 2-value case handles integrity-check branches: the hash check
/// produces a boolean that splits the dispatch into "pass" and "fail"
/// paths. Both are valid code addresses, so we pick the majority value
/// (the hash check is designed to pass for consistent VM contexts).
static std::optional<uint64_t>
trySpeculativeResolveToConstant(Value *V, Function &F,
                                const SpecStoreMap &SSM,
                                const DataLayout &DL,
                                const omill::BinaryMemoryMap *BMM) {
  constexpr unsigned NumTrials = 32;

  // Collect all allocas.
  SmallVector<AllocaInst *, 4> AllAllocas;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *A = dyn_cast<AllocaInst>(&I))
        AllAllocas.push_back(A);
  if (AllAllocas.empty())
    return std::nullopt;

  // Assigns every alloca a distinct base address.
  auto populateEnv = [&](DenseMap<Value *, uint64_t> &Env,
                         uint64_t StartBase) {
    uint64_t Base = StartBase;
    for (auto *A : AllAllocas) {
      Env[A] = Base;
      Base += 0x0001'0000'0000ULL; // 4GB separation
    }
  };

  auto runTrials = [&](uint64_t AllocaBase,
                       SmallVectorImpl<uint64_t> &Out) -> bool {
    for (unsigned Trial = 0; Trial < NumTrials; ++Trial) {
      DenseMap<Value *, uint64_t> Env;
      populateEnv(Env, AllocaBase);
      uint64_t RNG = 0xDEADBEEF12345678ULL ^
                     (uint64_t(Trial) * 0x9E3779B97F4A7C15ULL);
      SmallPtrSet<Value *, 32> InProgress;
      auto Res = concreteEval(V, Env, SSM, DL, InProgress, RNG);
      if (!Res) return false;
      Out.push_back(*Res);
    }
    return true;
  };

  // Run trials with base set 1.
  constexpr uint64_t AllocaBase1 = 0x7FFE'0000'0000ULL;
  SmallVector<uint64_t, 32> Results;
  if (!runTrials(AllocaBase1, Results))
    return std::nullopt;

  // Count distinct values and their frequencies.
  DenseMap<uint64_t, unsigned> Freq;
  for (auto R : Results) Freq[R]++;

  if (debugRecover()) {
    llvm::errs() << "  constant-eval: " << Freq.size()
                 << " distinct / " << NumTrials << " trials";
    for (auto &[V, C] : Freq)
      llvm::errs() << " 0x" << llvm::Twine::utohexstr(V) << "(" << C << ")";
    llvm::errs() << "\n";
  }

  uint64_t Candidate = 0;

  if (Freq.size() == 1) {
    Candidate = Freq.begin()->first;
  } else if (Freq.size() == 2 && BMM) {
    // Two-value split: integrity check branch. Pick the majority value
    // if it's a valid code address in the binary.
    uint64_t ValA = 0, ValB = 0;
    unsigned CountA = 0, CountB = 0;
    auto It = Freq.begin();
    ValA = It->first; CountA = It->second; ++It;
    ValB = It->first; CountB = It->second;

    // Check readability as proxy for "valid code address".
    uint8_t ByteA = 0, ByteB = 0;
    bool ValidA = BMM->read(ValA, &ByteA, 1);
    bool ValidB = BMM->read(ValB, &ByteB, 1);

    if (debugRecover())
      llvm::errs() << "  binary-check: A=0x" << llvm::Twine::utohexstr(ValA)
                   << (ValidA ? " valid" : " INVALID")
                   << " B=0x" << llvm::Twine::utohexstr(ValB)
                   << (ValidB ? " valid" : " INVALID") << "\n";

    if (ValidA && !ValidB) Candidate = ValA;
    else if (ValidB && !ValidA) Candidate = ValB;
    else if (ValidA && ValidB) {
      // Both valid — pick majority.
      Candidate = (CountA >= CountB) ? ValA : ValB;
      if (debugRecover())
        llvm::errs() << "  majority-vote: 0x"
                     << llvm::Twine::utohexstr(Candidate) << "\n";
    } else {
      return std::nullopt; // neither is valid code
    }
  } else {
    return std::nullopt; // 3+ distinct values = genuinely variable
  }

  // Cross-check: verify the candidate is NOT alloca-relative.
  constexpr uint64_t AllocaBase2 = 0x7FFF'0000'0000ULL;
  {
    DenseMap<Value *, uint64_t> Env;
    populateEnv(Env, AllocaBase2);
    uint64_t RNG = 0xDEADBEEF12345678ULL; // same seed as trial 0
    SmallPtrSet<Value *, 32> InProgress;
    auto Res = concreteEval(V, Env, SSM, DL, InProgress, RNG);
    if (!Res) return std::nullopt;
    if (Freq.size() == 1 && *Res != Candidate)
      return std::nullopt; // alloca-dependent
    if (Freq.size() == 2 && Freq.find(*Res) == Freq.end())
      return std::nullopt; // produced a THIRD value with different base
  }

  if (debugRecover())
    llvm::errs() << "  constant-resolve: 0x"
                 << llvm::Twine::utohexstr(Candidate) << "\n";
  return Candidate;
}
}  // namespace

namespace omill {

PreservedAnalyses
RecoverAllocaPointersPass::run(Function &F, FunctionAnalysisManager &AM) {
  // Skip remill semantics — they never have the patterns we're looking for.
  auto Name = F.getName();
  if (Name.starts_with("_ZN") || Name.starts_with("__remill_"))
    return PreservedAnalyses::all();
  const DataLayout &DL = F.getDataLayout();
  bool Changed = false;

  // Try to get BinaryMemoryMap for dispatch target validation.
  const omill::BinaryMemoryMap *BMM = nullptr;
  auto &MAMProxy = AM.getResult<ModuleAnalysisManagerFunctionProxy>(F);
  if (auto *Result =
          MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent()))
    BMM = Result;

  // Build i64-only store map for the linear resolution phase.
  StoreMap Stores = buildStoreMap(F, DL);

  SmallVector<IntToPtrInst *, 32> WorkList;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *I2P = dyn_cast<IntToPtrInst>(&I))
        WorkList.push_back(I2P);

  if (debugRecover())
    llvm::errs() << "[RecoverAllocaPointers] " << F.getName()
                 << ": " << WorkList.size() << " inttoptr instructions\n";

  // Phase 1: Linear resolution (add/sub chains, load forwarding).
  SmallVector<IntToPtrInst *, 16> Unresolved;
  for (auto *I2P : WorkList) {
    SmallPtrSet<Value *, 16> Visited;
    auto Res = resolveToAlloca(I2P->getOperand(0), DL, Stores, Visited);
    if (!Res) {
      Unresolved.push_back(I2P);
      continue;
    }

    auto *AllocaTy = Res->AI->getAllocatedType();
    auto AllocaSize = DL.getTypeAllocSize(AllocaTy);
    if (Res->Offset < 0 || static_cast<uint64_t>(Res->Offset) >= AllocaSize) {
      Unresolved.push_back(I2P);
      continue;
    }

    IRBuilder<> Builder(I2P);
    Value *GEP = Builder.CreateInBoundsGEP(Builder.getInt8Ty(), Res->AI,
                                           Builder.getInt64(Res->Offset));
    if (debugRecover())
      llvm::errs() << "  recovered: offset=" << Res->Offset
                   << " alloca=" << Res->AI->getName() << "\n";
    I2P->replaceAllUsesWith(GEP);
    Changed = true;
  }

  // Phase 2: Speculative concrete evaluation for remaining inttoptr.
  if (!Unresolved.empty()) {
    SpecStoreMap SSM = buildSpecStoreMap(F, DL);

    // Collect all allocas in the function for multi-alloca resolution.
    SmallVector<AllocaInst *, 4> AllAllocas;
    for (auto &BB : F)
      for (auto &I : BB)
        if (auto *A = dyn_cast<AllocaInst>(&I))
          AllAllocas.push_back(A);

    for (auto *I2P : Unresolved) {
      // Check if the expression tree references any alloca via ptrtoint.
      SmallPtrSet<Value *, 32> FindVisited;
      AllocaInst *HintAI = findAllocaInExpr(I2P->getOperand(0), SSM, DL, FindVisited);
      if (!HintAI) {
        // No alloca reference in expression — try constant resolution directly.
        auto ConstRes = trySpeculativeResolveToConstant(
            I2P->getOperand(0), F, SSM, DL, BMM);
        if (ConstRes) {
          auto *ConstVal = ConstantInt::get(I2P->getOperand(0)->getType(),
                                            *ConstRes);
          I2P->setOperand(0, ConstVal);
          if (debugRecover())
            llvm::errs() << "  constant-dispatch (no alloca hint): 0x"
                         << llvm::Twine::utohexstr(*ConstRes) << "\n";
          Changed = true;
        } else if (debugRecover()) {
          llvm::errs() << "  speculative: no alloca found for " << *I2P << "\n";
        }
        continue;
      }

      // Try resolving against each alloca in the function, starting with
      // the one found by findAllocaInExpr (most likely target).
      std::optional<AllocaOffset> Best;
      auto tryWithAI = [&](AllocaInst *AI) {
        if (Best) return;
        auto Res = trySpeculativeResolve(I2P->getOperand(0), AI, SSM, DL);
        if (!Res) return;
        auto *AllocaTy = Res->AI->getAllocatedType();
        auto AllocaSize = DL.getTypeAllocSize(AllocaTy);
        if (Res->Offset >= 0 &&
            static_cast<uint64_t>(Res->Offset) < AllocaSize)
          Best = Res;
      };

      // Try hint alloca first, then all others.
      tryWithAI(HintAI);
      for (auto *A : AllAllocas)
        if (A != HintAI) tryWithAI(A);

      if (!Best) {
        // Phase 2b: Try resolving to an absolute constant (dispatch target).
        // If the expression evaluates to the same constant regardless of
        // alloca bases and free variables, replace the operand with that constant.
        auto ConstRes = trySpeculativeResolveToConstant(
            I2P->getOperand(0), F, SSM, DL, BMM);
        if (ConstRes) {
          auto *ConstVal = ConstantInt::get(I2P->getOperand(0)->getType(),
                                            *ConstRes);
          I2P->setOperand(0, ConstVal);
          if (debugRecover())
            llvm::errs() << "  constant-dispatch: 0x"
                         << llvm::Twine::utohexstr(*ConstRes) << "\n";
          Changed = true;
        } else {
          if (debugRecover())
            llvm::errs() << "  speculative: FAILED for " << *I2P << "\n";
        }
        continue;
      }

      IRBuilder<> Builder(I2P);
      Value *GEP = Builder.CreateInBoundsGEP(Builder.getInt8Ty(), Best->AI,
                                             Builder.getInt64(Best->Offset));
      if (debugRecover())
        llvm::errs() << "  speculative: offset=" << Best->Offset
                     << " alloca=" << Best->AI->getName() << "\n";
      I2P->replaceAllUsesWith(GEP);
      Changed = true;
    }
  }

  // Clean up dead inttoptr instructions.
  for (auto *I2P : WorkList)
    if (I2P->use_empty())
      I2P->eraseFromParent();

  if (!Changed)
    return PreservedAnalyses::all();
  return PreservedAnalyses::none();
}

}  // namespace omill