#include "omill/Passes/IndirectCallResolver.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/ValueHandle.h>
#include <llvm/ADT/SmallPtrSet.h>

#include <map>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Maximum expression tree depth to prevent infinite recursion through PHIs.
static constexpr unsigned kMaxEvalDepth = 24;
/// Maximum Monte Carlo concrete-eval recursion depth.
static constexpr unsigned kMaxMCEvalDepth = 128;

/// Check if a pointer is a State struct GEP (getelementptr from arg0).
bool isStateGEP(llvm::Value *ptr) {
  auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr);
  if (!gep)
    return false;
  return llvm::isa<llvm::Argument>(gep->getPointerOperand());
}

/// Walk backwards in the same basic block from `load` looking for a store to
/// the same pointer.  Returns the stored Value* or nullptr.  Skips stores
/// through inttoptr (they can't alias State GEPs) and stops at calls.
llvm::Value *forwardLoadInBlock(llvm::LoadInst *load) {
  auto *BB = load->getParent();
  auto *load_ptr = load->getPointerOperand();
  bool load_is_state = isStateGEP(load_ptr);
  for (auto it = load->getIterator(); it != BB->begin();) {
    --it;
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it)) {
      if (SI->getPointerOperand() == load_ptr)
        return SI->getValueOperand();
      // If load is from State GEP, stores through inttoptr can't alias.
      if (load_is_state) {
        auto *sp = SI->getPointerOperand()->stripPointerCasts();
        if (llvm::isa<llvm::IntToPtrInst>(sp))
          continue;
      }
    }
    if (auto *CI2 = llvm::dyn_cast<llvm::CallInst>(&*it)) {
      auto *callee = CI2->getCalledFunction();
      if (callee && callee->isIntrinsic() &&
          (callee->doesNotAccessMemory() ||
           callee->onlyAccessesInaccessibleMemory()))
        continue;
      return nullptr;
    }
    if (llvm::isa<llvm::InvokeInst>(&*it))
      return nullptr;
  }
  return nullptr;
}

/// Normalize an integer address expression into (base, constant_offset).
/// Collapses chains of `add(add(X, A), B)` -> `(X, A+B)` and chases through
/// State GEP load->store forwarding.  Forwarding stops when it detects a
/// save/restore cycle (forwarded value resolves back to a load from the same
/// State GEP), which keeps both sides of a comparison at the same depth in
/// the RSP chain.
/// Returns (nullptr, C) for pure constants.
std::pair<llvm::Value *, int64_t> normalizeAddrExpr(llvm::Value *V,
                                                    unsigned max_fwd = 4) {
  int64_t offset = 0;
  unsigned fwd_remaining = max_fwd;
  while (true) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
      return {nullptr, offset + CI->getSExtValue()};
    // add(X, C) or add(C, X)
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
      if (BO->getOpcode() == llvm::Instruction::Add) {
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
          offset += C->getSExtValue();
          V = BO->getOperand(0);
          continue;
        }
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
          offset += C->getSExtValue();
          V = BO->getOperand(1);
          continue;
        }
      }
      if (BO->getOpcode() == llvm::Instruction::Sub) {
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
          offset -= C->getSExtValue();
          V = BO->getOperand(0);
          continue;
        }
      }
    }
    // Chase through State GEP loads via same-block store forwarding.
    if (fwd_remaining > 0) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
        if (isStateGEP(LI->getPointerOperand())) {
          if (auto *fwd = forwardLoadInBlock(LI)) {
            // Check if forwarding leads back to a load from the same State
            // GEP (save/restore cycle, e.g. RSP save then RSP restore).
            // If so, stop: this load is the canonical base.
            auto [fwd_base, fwd_off] = normalizeAddrExpr(fwd, 0);
            if (auto *fwd_load = llvm::dyn_cast_or_null<llvm::LoadInst>(fwd_base)) {
              if (fwd_load->getPointerOperand() == LI->getPointerOperand()) {
                // Cycle detected: forwarded value is another load from the
                // same register.  Use current load as canonical base.
                return {V, offset};
              }
            }
            --fwd_remaining;
            V = fwd;
            continue;
          }
        }
      }
    }
    return {V, offset};
  }
}

/// Check if two address-expression bases are equivalent.
/// Handles: SSA equality, and loads-from-same-State-GEP where one
/// store-forwards to the other (one level).
bool addressBasesEqual(llvm::Value *A, llvm::Value *B) {
  if (A == B)
    return true;
  // Both must be loads from the same pointer (State GEP).
  auto *LA = llvm::dyn_cast_or_null<llvm::LoadInst>(A);
  auto *LB = llvm::dyn_cast_or_null<llvm::LoadInst>(B);
  if (!LA || !LB)
    return false;
  if (LA->getPointerOperand() != LB->getPointerOperand())
    return false;
  // Try forwarding one level: does A forward to a value equal to B,
  // or B forward to a value equal to A?
  if (auto *fwdA = forwardLoadInBlock(LA)) {
    auto [baseA, offA] = normalizeAddrExpr(fwdA, 0);
    if (offA == 0 && baseA == B)
      return true;
  }
  if (auto *fwdB = forwardLoadInBlock(LB)) {
    auto [baseB, offB] = normalizeAddrExpr(fwdB, 0);
    if (offB == 0 && baseB == A)
      return true;
  }
  return false;
}

/// Recursively evaluate an SSA value to a concrete uint64_t using binary
/// memory reads for loads from constant addresses.
///
/// This is the core of the pass: unlike ConstantMemoryFolding (which folds
/// individual loads) or InstCombine (which folds arithmetic), this evaluator
/// walks the entire expression tree in one shot, resolving multi-hop chains
/// like load(load(0x140008000) + 0x10) without requiring multiple pass
/// iterations.
std::optional<uint64_t> evaluateToConstantImpl(
    llvm::Value *V, const BinaryMemoryMap &map,
    llvm::SmallPtrSetImpl<llvm::Value *> &Visited, unsigned depth = 0) {
  if (depth > kMaxEvalDepth)
    return std::nullopt;
  if (!Visited.insert(V).second)
    return std::nullopt;  // Cycle through PHIs.

  // Function argument: arg1 in lifted functions is the entry PC.
  // The function name encodes it as sub_<hex_va>.
  if (auto *Arg = llvm::dyn_cast<llvm::Argument>(V)) {
    if (Arg->getArgNo() == 1) {  // program_counter
      auto *F = Arg->getParent();
      auto name = F->getName();
      uint64_t va = extractEntryVA(name);
      if (va != 0)
        return va;
    }
    return std::nullopt;
  }

  // Already a constant integer.
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    if (CI->getBitWidth() <= 64)
      return CI->getZExtValue();
    return std::nullopt;
  }

  // ZExt / SExt: evaluate the inner value.
  if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(V))
    return evaluateToConstantImpl(zext->getOperand(0), map, Visited, depth + 1);
  if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(V)) {
    auto inner = evaluateToConstantImpl(sext->getOperand(0), map, Visited, depth + 1);
    if (!inner)
      return std::nullopt;
    unsigned src_bits = sext->getOperand(0)->getType()->getIntegerBitWidth();
    // Sign extend from src_bits to 64 bits.
    uint64_t val = *inner;
    if (src_bits < 64 && (val & (1ULL << (src_bits - 1))))
      val |= ~((1ULL << src_bits) - 1);
    return val;
  }

  // Trunc: evaluate inner and mask.
  if (auto *trunc = llvm::dyn_cast<llvm::TruncInst>(V)) {
    auto inner = evaluateToConstantImpl(trunc->getOperand(0), map, Visited, depth + 1);
    if (!inner)
      return std::nullopt;
    unsigned dst_bits = trunc->getType()->getIntegerBitWidth();
    if (dst_bits >= 64)
      return *inner;
    return *inner & ((1ULL << dst_bits) - 1);
  }

  // Binary operators: add, sub, xor, or, and, shl, lshr, ashr, mul.
  if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto lhs = evaluateToConstantImpl(bin->getOperand(0), map, Visited, depth + 1);
    auto rhs = evaluateToConstantImpl(bin->getOperand(1), map, Visited, depth + 1);
    if (!lhs || !rhs)
      return std::nullopt;

    switch (bin->getOpcode()) {
    case llvm::Instruction::Add:  return *lhs + *rhs;
    case llvm::Instruction::Sub:  return *lhs - *rhs;
    case llvm::Instruction::Mul:  return *lhs * *rhs;
    case llvm::Instruction::Xor:  return *lhs ^ *rhs;
    case llvm::Instruction::Or:   return *lhs | *rhs;
    case llvm::Instruction::And:  return *lhs & *rhs;
    case llvm::Instruction::Shl:  return (*rhs < 64) ? (*lhs << *rhs) : 0ULL;
    case llvm::Instruction::LShr: return (*rhs < 64) ? (*lhs >> *rhs) : 0ULL;
    case llvm::Instruction::AShr: {
      if (*rhs >= 64)
        return (*lhs & (1ULL << 63)) ? ~0ULL : 0ULL;
      return static_cast<uint64_t>(
          static_cast<int64_t>(*lhs) >> static_cast<int64_t>(*rhs));
    }
    default:
      return std::nullopt;
    }
  }

  // Load: try binary memory read, then same-block store forwarding.
  if (auto *load = llvm::dyn_cast<llvm::LoadInst>(V)) {
    auto *ptr = load->getPointerOperand()->stripPointerCasts();
    // Detect inttoptr addressing.
    llvm::Value *int_val = nullptr;
    if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
      int_val = itp->getOperand(0);
    else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
      if (ce->getOpcode() == llvm::Instruction::IntToPtr)
        int_val = ce->getOperand(0);
    }

    // Path 1: inttoptr(X) where X evaluates to a constant → binary memory read.
    if (int_val) {
      auto addr = evaluateToConstantImpl(int_val, map, Visited, depth + 1);
      if (addr) {
        unsigned load_size = load->getType()->getIntegerBitWidth() / 8;
        if (load_size <= 8) {
          uint8_t buf[8] = {};
          if (map.read(*addr, buf, load_size)) {
            uint64_t result = 0;
            for (unsigned i = 0; i < load_size; ++i)
              result |= static_cast<uint64_t>(buf[i]) << (i * 8);
            unsigned bits = load->getType()->getIntegerBitWidth();
            if (bits < 64)
              result &= (1ULL << bits) - 1;
            return result;
          }
        }
      }
    }

    // Path 2: Same-block store-to-load forwarding.
    // Handles two cases:
    //  a) Exact pointer match (State GEP stores, e.g. load %R12 / store %R12)
    //  b) Symbolic inttoptr address match (computed-address stores/loads
    //     that share the same (base,offset) after normalization)
    auto *BB = load->getParent();
    auto *load_ptr = load->getPointerOperand();
    bool load_is_state_gep = isStateGEP(load_ptr);
    auto load_addr_norm = int_val
        ? std::optional(normalizeAddrExpr(int_val))
        : std::nullopt;
    for (auto it = load->getIterator(); it != BB->begin();) {
      --it;
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it)) {
        auto *store_ptr = SI->getPointerOperand();

        // Case (a): exact pointer match (same GEP/alloca/SSA value).
        if (store_ptr == load_ptr) {
          return evaluateToConstantImpl(SI->getValueOperand(), map, Visited, depth + 1);
        }

        // Classify the store pointer.
        auto *sp_stripped = store_ptr->stripPointerCasts();
        bool store_is_inttoptr = llvm::isa<llvm::IntToPtrInst>(sp_stripped);
        bool store_is_state_gep = isStateGEP(store_ptr);

        if (int_val) {
          // Load is from inttoptr.  Check symbolic address match.
          if (store_is_inttoptr) {
            llvm::Value *store_int_val = nullptr;
            if (auto *itp2 = llvm::dyn_cast<llvm::IntToPtrInst>(sp_stripped))
              store_int_val = itp2->getOperand(0);

            if (store_int_val) {
              // Fast path: same SSA address.
              if (store_int_val == int_val) {
                return evaluateToConstantImpl(SI->getValueOperand(), map, Visited, depth + 1);
              }

              // Normalize both address expressions and compare.
              auto [loadBase, loadOff] = *load_addr_norm;
              auto [storeBase, storeOff] = normalizeAddrExpr(store_int_val);
              if (loadOff == storeOff &&
                  addressBasesEqual(loadBase, storeBase)) {
                return evaluateToConstantImpl(SI->getValueOperand(), map,
                                             Visited, depth + 1);
              }
            }
            // Non-matching inttoptr store — skip (different runtime addr).
            continue;
          }
          // Store to State GEP or other — can't alias inttoptr load.
          if (store_is_state_gep)
            continue;
        } else if (load_is_state_gep) {
          // Load is from State GEP.
          if (store_is_inttoptr)
            continue;  // inttoptr store can't alias State GEP
          if (store_is_state_gep)
            continue;  // Different State GEP — different register
        }
        // Unknown store — conservatively stop walking.
        break;
      }
      // Stop at call/invoke that may modify memory.
      if (auto *CI2 = llvm::dyn_cast<llvm::CallInst>(&*it)) {
        auto *callee = CI2->getCalledFunction();
        if (callee && callee->isIntrinsic() &&
            (callee->doesNotAccessMemory() ||
             callee->onlyAccessesInaccessibleMemory()))
          continue;
        break;
      }
      if (llvm::isa<llvm::InvokeInst>(&*it))
        break;
    }

    return std::nullopt;
  }

  // Select with one evaluable arm (or both).
  if (auto *sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
    auto cond = evaluateToConstantImpl(sel->getCondition(), map, Visited, depth + 1);
    if (cond) {
      // Condition is known — evaluate only the selected arm.
      auto *arm = (*cond != 0) ? sel->getTrueValue() : sel->getFalseValue();
      return evaluateToConstantImpl(arm, map, Visited, depth + 1);
    }
    // If both arms evaluate to the same value, use that.
    auto true_val = evaluateToConstantImpl(sel->getTrueValue(), map, Visited, depth + 1);
    auto false_val = evaluateToConstantImpl(sel->getFalseValue(), map, Visited, depth + 1);
    if (true_val && false_val && *true_val == *false_val)
      return *true_val;
    return std::nullopt;
  }

  // PHI with all evaluable incoming values that agree.
  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(V)) {
    if (phi->getNumIncomingValues() == 0)
      return std::nullopt;
    std::optional<uint64_t> agreed;
    for (unsigned i = 0, e = phi->getNumIncomingValues(); i < e; ++i) {
      auto val = evaluateToConstantImpl(phi->getIncomingValue(i), map, Visited, depth + 1);
      if (!val)
        return std::nullopt;
      if (!agreed)
        agreed = val;
      else if (*agreed != *val)
        return std::nullopt;
    }
    return agreed;
  }

  return std::nullopt;
}

/// Public wrapper — creates a per-call visited set for cycle detection.
std::optional<uint64_t> evaluateToConstant(llvm::Value *V,
                                           const BinaryMemoryMap &map) {
  llvm::SmallPtrSet<llvm::Value *, 32> Visited;
  return evaluateToConstantImpl(V, map, Visited);
}

// ============================================================
// Monte Carlo Concrete Evaluation for VM Dispatch Targets
// ============================================================
// When the deterministic evaluateToConstant fails (because some operands
// are symbolic — e.g., unknown register values from the caller), we fall
// back to Monte Carlo evaluation.  VM dispatch targets are deterministic:
// symbolic operands are mixed via MBA but cancel out, always producing
// the same constant.  We verify this by running multiple trials with
// different random values for unknowns and checking consistency.

/// Map from {AllocaInst*, byte_offset} to stored values.
struct MCStoreEntry {
  llvm::WeakTrackingVH Val;
  unsigned BitWidth;
  llvm::WeakTrackingVH SI;
};
using MCStoreMap = llvm::DenseMap<std::pair<llvm::AllocaInst *, int64_t>,
                                  llvm::SmallVector<MCStoreEntry, 2>>;

/// Decompose a GEP to {alloca, byte_offset}.
static std::optional<std::pair<llvm::AllocaInst *, int64_t>>
mcDecomposeGEP(llvm::Value *Ptr, const llvm::DataLayout &DL) {
  if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(Ptr))
    return std::make_pair(AI, int64_t(0));
  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(Ptr)) {
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(GEP->getPointerOperand())) {
      llvm::APInt Off(64, 0);
      if (GEP->accumulateConstantOffset(DL, Off))
        return std::make_pair(AI, Off.getSExtValue());
    }
  }
  return std::nullopt;
}

/// Build a store map tracking all integer-type stores to alloca-based GEPs.
static MCStoreMap buildMCStoreMap(llvm::Function &F,
                                   const llvm::DataLayout &DL) {
  MCStoreMap Map;
  for (auto &BB : F)
    for (auto &I : BB) {
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI)
        continue;
      auto *ValTy = SI->getValueOperand()->getType();
      if (!ValTy->isIntegerTy())
        continue;
      auto Decomp = mcDecomposeGEP(SI->getPointerOperand(), DL);
      if (!Decomp)
        continue;
      Map[*Decomp].push_back(
          {llvm::WeakTrackingVH(SI->getValueOperand()),
           ValTy->getIntegerBitWidth(), llvm::WeakTrackingVH(SI)});
    }
  return Map;
}

/// Advance a simple xorshift64 PRNG.
static uint64_t mcXorshift64(uint64_t &S) {
  S ^= S << 13;
  S ^= S >> 7;
  S ^= S << 17;
  return S;
}

/// Concrete evaluation of an integer expression tree.
/// Unknown leaves (arguments, unresolved loads, PHIs, calls) get random
/// values from the RNG.  The SpecStoreMap enables following loads through
/// alloca-based stores.
static std::optional<uint64_t>
mcConcreteEval(llvm::Value *V,
               llvm::DenseMap<llvm::Value *, uint64_t> &Env,
               const MCStoreMap &SSM,
               const llvm::DataLayout &DL,
               const BinaryMemoryMap *BMM,
               llvm::SmallPtrSetImpl<llvm::Value *> &InProgress,
               uint64_t &RNG,
               unsigned Depth = 0) {
  if (Depth > kMaxMCEvalDepth)
    return std::nullopt;

  auto CIt = Env.find(V);
  if (CIt != Env.end())
    return CIt->second;
  if (!InProgress.insert(V).second)
    return std::nullopt;

  std::optional<uint64_t> Result;

  // Function argument: arg1 in lifted functions is the entry PC.
  if (auto *Arg = llvm::dyn_cast<llvm::Argument>(V)) {
    if (Arg->getArgNo() == 1) {
      uint64_t va = extractEntryVA(Arg->getParent()->getName());
      if (va != 0)
        Result = va;
    }
    // Other arguments (State ptr, memory) stay unresolved → random below.
  } else if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    // Wide constants (i128+ from XMM ops) can't be represented in uint64_t.
    if (CI->getBitWidth() <= 64)
      Result = CI->getZExtValue();
  } else if (llvm::isa<llvm::UndefValue>(V) || llvm::isa<llvm::PoisonValue>(V)) {
    Result = uint64_t(0);
  } else if (auto *P2I = llvm::dyn_cast<llvm::PtrToIntInst>(V)) {
    llvm::Value *Ptr = P2I->getOperand(0);
    if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(Ptr)) {
      auto It = Env.find(AI);
      if (It != Env.end())
        Result = It->second;
    } else if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(Ptr)) {
      if (auto *AI =
              llvm::dyn_cast<llvm::AllocaInst>(GEP->getPointerOperand())) {
        auto It = Env.find(AI);
        if (It != Env.end()) {
          llvm::APInt Off(64, 0);
          if (GEP->accumulateConstantOffset(DL, Off))
            Result = It->second + Off.getZExtValue();
        }
      }
    }
  } else if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
    if (LI->getType()->isIntegerTy()) {
      unsigned LoadBW = LI->getType()->getIntegerBitWidth();
      // Try alloca store map first.
      auto Decomp = mcDecomposeGEP(LI->getPointerOperand(), DL);
      if (Decomp) {
        auto SIt = SSM.find(*Decomp);
        if (SIt != SSM.end()) {
          llvm::Value *BestVal = nullptr;
          for (auto &E : SIt->second) {
            if (E.BitWidth != LoadBW)
              continue;
            auto *StoreI = llvm::dyn_cast_or_null<llvm::StoreInst>(E.SI);
            llvm::Value *StoreVal = E.Val;
            if (!StoreI || !StoreVal)
              continue;
            if (StoreI->getParent() == LI->getParent()) {
              if (StoreI->comesBefore(LI))
                BestVal = StoreVal;
            } else {
              BestVal = StoreVal;
            }
          }
          if (BestVal)
            Result =
                mcConcreteEval(BestVal, Env, SSM, DL, BMM, InProgress, RNG,
                               Depth + 1);
        }
      }
      // Phase 1.5: Same-BB inttoptr store forwarding.
      // Walk backward in the same basic block looking for a store to
      // an inttoptr address that concretely evaluates to the same
      // address as the load.  This handles VM handlers where stores
      // and loads go through inttoptr(RSP + offset) patterns that
      // LLVM's AA can't prove NoAlias for intervening stores.
      if (!Result) {
        auto *Ptr = LI->getPointerOperand()->stripPointerCasts();
        llvm::Value *LoadIntVal = nullptr;
        if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(Ptr))
          LoadIntVal = ITP->getOperand(0);
        if (LoadIntVal) {
          auto LoadAddr =
              mcConcreteEval(LoadIntVal, Env, SSM, DL, BMM, InProgress, RNG,
                             Depth + 1);
          if (LoadAddr) {
            auto *BB = LI->getParent();
            for (auto It = LI->getIterator(); It != BB->begin();) {
              --It;
              if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*It)) {
                if (!SI->getValueOperand()->getType()->isIntegerTy())
                  continue;
                if (SI->getValueOperand()->getType()->getIntegerBitWidth() !=
                    LoadBW)
                  continue;
                auto *SP = SI->getPointerOperand()->stripPointerCasts();
                if (auto *SITP = llvm::dyn_cast<llvm::IntToPtrInst>(SP)) {
                  auto StoreAddr = mcConcreteEval(
                      SITP->getOperand(0), Env, SSM, DL, BMM, InProgress, RNG,
                      Depth + 1);
                  if (StoreAddr && *StoreAddr == *LoadAddr) {
                    Result = mcConcreteEval(SI->getValueOperand(), Env, SSM, DL,
                                            BMM, InProgress, RNG, Depth + 1);
                    break;
                  }
                }
              } else if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&*It)) {
                // Stop at calls that may write memory.
                if (!CI->doesNotAccessMemory())
                  break;
              }
            }
          }
        }
      }
      // Try binary memory read for inttoptr loads.
      if (!Result && BMM) {
        auto *Ptr = LI->getPointerOperand()->stripPointerCasts();
        llvm::Value *IntVal = nullptr;
        if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(Ptr))
          IntVal = ITP->getOperand(0);
        if (IntVal) {
          auto Addr =
              mcConcreteEval(IntVal, Env, SSM, DL, BMM, InProgress, RNG,
                             Depth + 1);
          if (Addr) {
            unsigned LoadSize = LoadBW / 8;
            if (LoadSize <= 8) {
              uint8_t Buf[8] = {};
              if (BMM->read(*Addr, Buf, LoadSize)) {
                uint64_t Val = 0;
                for (unsigned i = 0; i < LoadSize; ++i)
                  Val |= static_cast<uint64_t>(Buf[i]) << (i * 8);
                if (LoadBW < 64)
                  Val &= (1ULL << LoadBW) - 1;
                Result = Val;
              }
            }
          }
        }
      }
    }
  } else if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto L = mcConcreteEval(BO->getOperand(0), Env, SSM, DL, BMM, InProgress,
                            RNG, Depth + 1);
    auto R = mcConcreteEval(BO->getOperand(1), Env, SSM, DL, BMM, InProgress,
                            RNG, Depth + 1);
    if (L && R) {
      switch (BO->getOpcode()) {
      case llvm::Instruction::Add:  Result = *L + *R; break;
      case llvm::Instruction::Sub:  Result = *L - *R; break;
      case llvm::Instruction::Mul:  Result = *L * *R; break;
      case llvm::Instruction::Xor:  Result = *L ^ *R; break;
      case llvm::Instruction::And:  Result = *L & *R; break;
      case llvm::Instruction::Or:   Result = *L | *R; break;
      case llvm::Instruction::Shl:  Result = *L << (*R & 63); break;
      case llvm::Instruction::LShr: Result = *L >> (*R & 63); break;
      case llvm::Instruction::AShr:
        Result = static_cast<uint64_t>(
            static_cast<int64_t>(*L) >> (*R & 63));
        break;
      case llvm::Instruction::URem:
        Result = *R ? std::optional(*L % *R) : std::nullopt;
        break;
      case llvm::Instruction::UDiv:
        Result = *R ? std::optional(*L / *R) : std::nullopt;
        break;
      default: break;
      }
    }
  } else if (auto *Cast = llvm::dyn_cast<llvm::CastInst>(V)) {
    auto Op =
        mcConcreteEval(Cast->getOperand(0), Env, SSM, DL, BMM, InProgress, RNG,
                       Depth + 1);
    if (Op) {
      unsigned SrcBits = Cast->getSrcTy()->getScalarSizeInBits();
      unsigned DstBits = Cast->getDestTy()->getScalarSizeInBits();
      switch (Cast->getOpcode()) {
      case llvm::Instruction::ZExt:
        Result = (SrcBits < 64) ? (*Op & ((1ULL << SrcBits) - 1)) : *Op;
        break;
      case llvm::Instruction::SExt: {
        uint64_t v = *Op;
        if (SrcBits < 64) {
          v &= (1ULL << SrcBits) - 1;
          if (v & (1ULL << (SrcBits - 1)))
            v |= ~((1ULL << SrcBits) - 1);
        }
        Result = v;
        break;
      }
      case llvm::Instruction::Trunc:
        Result = (DstBits < 64) ? (*Op & ((1ULL << DstBits) - 1)) : *Op;
        break;
      case llvm::Instruction::BitCast:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::IntToPtr:
        Result = *Op;
        break;
      default: break;
      }
    }
  } else if (auto *IC = llvm::dyn_cast<llvm::ICmpInst>(V)) {
    auto L = mcConcreteEval(IC->getOperand(0), Env, SSM, DL, BMM, InProgress,
                            RNG, Depth + 1);
    auto R = mcConcreteEval(IC->getOperand(1), Env, SSM, DL, BMM, InProgress,
                            RNG, Depth + 1);
    if (L && R) {
      bool Res = false;
      switch (IC->getPredicate()) {
      case llvm::ICmpInst::ICMP_EQ:  Res = *L == *R; break;
      case llvm::ICmpInst::ICMP_NE:  Res = *L != *R; break;
      case llvm::ICmpInst::ICMP_UGT: Res = *L > *R; break;
      case llvm::ICmpInst::ICMP_UGE: Res = *L >= *R; break;
      case llvm::ICmpInst::ICMP_ULT: Res = *L < *R; break;
      case llvm::ICmpInst::ICMP_ULE: Res = *L <= *R; break;
      case llvm::ICmpInst::ICMP_SGT:
        Res = static_cast<int64_t>(*L) > static_cast<int64_t>(*R); break;
      case llvm::ICmpInst::ICMP_SGE:
        Res = static_cast<int64_t>(*L) >= static_cast<int64_t>(*R); break;
      case llvm::ICmpInst::ICMP_SLT:
        Res = static_cast<int64_t>(*L) < static_cast<int64_t>(*R); break;
      case llvm::ICmpInst::ICMP_SLE:
        Res = static_cast<int64_t>(*L) <= static_cast<int64_t>(*R); break;
      default: goto mc_done;
      }
      Result = Res ? 1ULL : 0ULL;
    }
  } else if (auto *Sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
    auto Cond =
        mcConcreteEval(Sel->getCondition(), Env, SSM, DL, BMM, InProgress, RNG,
                       Depth + 1);
    if (Cond)
      Result = (*Cond & 1)
          ? mcConcreteEval(Sel->getTrueValue(), Env, SSM, DL, BMM, InProgress,
                           RNG, Depth + 1)
          : mcConcreteEval(Sel->getFalseValue(), Env, SSM, DL, BMM, InProgress,
                           RNG, Depth + 1);
  } else if (auto *PHI = llvm::dyn_cast<llvm::PHINode>(V)) {
    // For PHI nodes, try evaluating all incoming values.
    // If they all agree, use that.  Otherwise treat as free variable.
    if (PHI->getNumIncomingValues() > 0) {
      // Try control-flow-aware evaluation: for each predecessor with a
      // conditional branch, evaluate the condition to determine which
      // incoming value to use.  This handles SHR switch patterns where
      // different paths produce different values but the final result
      // is deterministic.
      if (PHI->getNumIncomingValues() == 2) {
        auto *BB0 = PHI->getIncomingBlock(0);
        auto *BB1 = PHI->getIncomingBlock(1);
        // Check if both predecessors share a common dominating conditional
        // branch.  Common pattern: br i1 %cond, label %BB0, label %BB1
        llvm::BranchInst *CondBr = nullptr;
        if (auto *BI = llvm::dyn_cast<llvm::BranchInst>(BB0->getTerminator()))
          if (BI->isConditional() &&
              ((BI->getSuccessor(0) == PHI->getParent() &&
                BI->getSuccessor(1) == PHI->getParent()) ||
               BI->getSuccessor(0) == BB1 || BI->getSuccessor(1) == BB1))
            CondBr = BI;
        if (!CondBr)
          if (auto *BI = llvm::dyn_cast<llvm::BranchInst>(BB1->getTerminator()))
            if (BI->isConditional() &&
                ((BI->getSuccessor(0) == PHI->getParent() &&
                  BI->getSuccessor(1) == PHI->getParent()) ||
                 BI->getSuccessor(0) == BB0 || BI->getSuccessor(1) == BB0))
              CondBr = BI;
        if (CondBr) {
          auto cond = mcConcreteEval(CondBr->getCondition(), Env, SSM, DL, BMM,
                                      InProgress, RNG, Depth + 1);
          if (cond) {
            // Determine which successor is taken.
            auto *taken_succ = (*cond & 1) ? CondBr->getSuccessor(0)
                                            : CondBr->getSuccessor(1);
            // Find the incoming value from the taken path.
            for (unsigned i = 0; i < 2; ++i) {
              auto *inc_bb = PHI->getIncomingBlock(i);
              // The taken successor might be the incoming block itself,
              // or the incoming block might be reachable from the taken
              // successor (for multi-block diamond patterns).
              if (inc_bb == taken_succ ||
                  inc_bb == CondBr->getParent()) {
                Result = mcConcreteEval(PHI->getIncomingValue(i), Env, SSM, DL,
                                         BMM, InProgress, RNG, Depth + 1);
                break;
              }
            }
          }
        }
      }
      // Fallback: check if all incoming values agree.
      if (!Result) {
        std::optional<uint64_t> agreed;
        bool all_agree = true;
        for (unsigned i = 0, e = PHI->getNumIncomingValues(); i < e; ++i) {
          auto val = mcConcreteEval(PHI->getIncomingValue(i), Env, SSM, DL, BMM,
                                    InProgress, RNG, Depth + 1);
          if (!val) {
            all_agree = false;
            break;
          }
          if (!agreed)
            agreed = val;
          else if (*agreed != *val) {
            all_agree = false;
            break;
          }
        }
        if (all_agree && agreed)
          Result = *agreed;
      }
    }
  }

mc_done:
  InProgress.erase(V);

  // Unknown leaves get random concrete values.
  if (!Result) {
    if (llvm::isa<llvm::Argument>(V) || llvm::isa<llvm::PHINode>(V) ||
        llvm::isa<llvm::CallBase>(V) || llvm::isa<llvm::LoadInst>(V)) {
      Result = mcXorshift64(RNG);
    } else {
      return std::nullopt;
    }
  }

  Env[V] = *Result;
  return *Result;
}

/// Try to resolve a dispatch target using Monte Carlo evaluation.
/// Returns the constant value if all trials produce the same result
/// and the result is a valid address in the binary.
static std::optional<uint64_t>
tryMonteCarloResolve(llvm::Value *V, llvm::Function &F,
                     const BinaryMemoryMap *BMM,
                     const MCStoreMap *CachedSSM = nullptr) {
  constexpr unsigned NumTrials = 32;
  const llvm::DataLayout &DL = F.getDataLayout();

  // Use the cached store map if provided, otherwise build one.
  MCStoreMap LocalSSM;
  if (!CachedSSM) {
    LocalSSM = buildMCStoreMap(F, DL);
    CachedSSM = &LocalSSM;
  }
  const MCStoreMap &SSM = *CachedSSM;

  // Collect all allocas for base assignment.
  llvm::SmallVector<llvm::AllocaInst *, 8> AllAllocas;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *A = llvm::dyn_cast<llvm::AllocaInst>(&I))
        AllAllocas.push_back(A);

  auto populateAllocaBases = [&](llvm::DenseMap<llvm::Value *, uint64_t> &Env,
                                  uint64_t StartBase) {
    uint64_t Base = StartBase;
    for (auto *A : AllAllocas) {
      Env[A] = Base;
      Base += 0x0001'0000'0000ULL;
    }
  };

  // Run trials with first alloca base set.
  constexpr uint64_t AllocaBase1 = 0x7FFE'0000'0000ULL;
  llvm::DenseMap<uint64_t, unsigned> Freq;

  for (unsigned Trial = 0; Trial < NumTrials; ++Trial) {
    llvm::DenseMap<llvm::Value *, uint64_t> Env;
    populateAllocaBases(Env, AllocaBase1);
    uint64_t RNG = 0xDEADBEEF12345678ULL ^
                   (uint64_t(Trial) * 0x9E3779B97F4A7C15ULL);
    llvm::SmallPtrSet<llvm::Value *, 32> InProgress;
    auto Res = mcConcreteEval(V, Env, SSM, DL, BMM, InProgress, RNG);
    if (!Res)
      return std::nullopt;
    Freq[*Res]++;
  }

  uint64_t Candidate = 0;

  if (Freq.size() == 1) {
    Candidate = Freq.begin()->first;
  } else if (Freq.size() == 2 && BMM) {
    // Two-value split: integrity check branch.  Pick the majority value
    // if it's a valid binary address.
    auto It = Freq.begin();
    uint64_t ValA = It->first;
    unsigned CountA = It->second;
    ++It;
    uint64_t ValB = It->first;
    unsigned CountB = It->second;

    uint8_t ByteA = 0, ByteB = 0;
    bool ValidA = BMM->read(ValA, &ByteA, 1);
    bool ValidB = BMM->read(ValB, &ByteB, 1);

    if (ValidA && !ValidB)
      Candidate = ValA;
    else if (ValidB && !ValidA)
      Candidate = ValB;
    else if (ValidA && ValidB)
      Candidate = (CountA >= CountB) ? ValA : ValB;
    else
      return std::nullopt;
  } else {
    return std::nullopt;
  }

  // Cross-check: verify the result is NOT alloca-dependent.
  constexpr uint64_t AllocaBase2 = 0x7FFF'0000'0000ULL;
  {
    llvm::DenseMap<llvm::Value *, uint64_t> Env;
    populateAllocaBases(Env, AllocaBase2);
    uint64_t RNG = 0xDEADBEEF12345678ULL; // same seed as trial 0
    llvm::SmallPtrSet<llvm::Value *, 32> InProgress;
    auto Res = mcConcreteEval(V, Env, SSM, DL, BMM, InProgress, RNG);
    if (!Res)
      return std::nullopt;
    if (Freq.size() == 1 && *Res != Candidate)
      return std::nullopt; // alloca-dependent
    if (Freq.size() == 2 && Freq.find(*Res) == Freq.end())
      return std::nullopt; // third distinct value
  }

  // Validate: candidate should be a valid binary address (if BMM available).
  if (BMM) {
    uint8_t Byte = 0;
    if (!BMM->read(Candidate, &Byte, 1))
      return std::nullopt;
  }

  return Candidate;
}

// ============================================================
// Forward Concrete Interpreter for Cross-BB Dispatch Resolution
// ============================================================
// When the backward MC evaluator fails (because stores and loads go through
// inttoptr addresses in different basic blocks), we use a forward interpreter
// that walks the function from entry, executing instructions in order.  This
// naturally handles cross-BB store forwarding through a byte-addressable
// virtual memory map, and resolves PHI nodes by tracking the execution path.

/// Store bytes to virtual memory (little-endian).
static void virtMemStore(std::map<uint64_t, uint8_t> &Mem,
                          uint64_t Addr, uint64_t Val, unsigned Bytes) {
  for (unsigned i = 0; i < Bytes; ++i)
    Mem[Addr + i] = static_cast<uint8_t>((Val >> (i * 8)) & 0xFF);
}

/// Load bytes from virtual memory (little-endian).
/// Returns nullopt if any byte is missing.
static std::optional<uint64_t> virtMemLoad(
    const std::map<uint64_t, uint8_t> &Mem,
    uint64_t Addr, unsigned Bytes) {
  uint64_t Result = 0;
  for (unsigned i = 0; i < Bytes; ++i) {
    auto It = Mem.find(Addr + i);
    if (It == Mem.end())
      return std::nullopt;
    Result |= static_cast<uint64_t>(It->second) << (i * 8);
  }
  return Result;
}

/// Get a concrete value for an SSA value from the environment or constants.
static uint64_t fwdGetVal(llvm::Value *V,
                           llvm::DenseMap<llvm::Value *, uint64_t> &Env,
                           uint64_t &RNG) {
  auto It = Env.find(V);
  if (It != Env.end())
    return It->second;
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    if (CI->getBitWidth() <= 64)
      return CI->getZExtValue();
    return CI->getValue().trunc(64).getZExtValue();
  }
  if (llvm::isa<llvm::UndefValue>(V) || llvm::isa<llvm::PoisonValue>(V))
    return 0;
  if (auto *CFP = llvm::dyn_cast<llvm::ConstantFP>(V)) {
    auto Bits = CFP->getValueAPF().bitcastToAPInt();
    if (Bits.getBitWidth() <= 64)
      return Bits.getZExtValue();
    return Bits.trunc(64).getZExtValue();
  }
  if (llvm::isa<llvm::ConstantAggregateZero>(V) ||
      llvm::isa<llvm::ConstantPointerNull>(V))
    return 0;
  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr ||
        CE->getOpcode() == llvm::Instruction::PtrToInt ||
        CE->getOpcode() == llvm::Instruction::BitCast)
      return fwdGetVal(CE->getOperand(0), Env, RNG);
  }
  if (auto *CDV = llvm::dyn_cast<llvm::ConstantDataVector>(V)) {
    unsigned NumElems = CDV->getNumElements();
    unsigned ElemBits = CDV->getElementType()->getScalarSizeInBits();
    if (NumElems * ElemBits <= 64) {
      uint64_t Result = 0;
      for (unsigned i = 0; i < NumElems; ++i) {
        uint64_t Elem = 0;
        if (CDV->getElementType()->isFloatTy()) {
          float F = CDV->getElementAsFloat(i);
          std::memcpy(&Elem, &F, 4);
        } else if (CDV->getElementType()->isDoubleTy()) {
          double D = CDV->getElementAsDouble(i);
          std::memcpy(&Elem, &D, 8);
        } else if (CDV->getElementType()->isIntegerTy()) {
          Elem = CDV->getElementAsInteger(i);
        }
        uint64_t Mask = (ElemBits < 64) ? ((1ULL << ElemBits) - 1) : ~0ULL;
        Result |= (Elem & Mask) << (i * ElemBits);
      }
      return Result;
    }
  }
  return mcXorshift64(RNG);
}

/// Run one forward interpretation trial from function entry to a dispatch call.
/// Returns the concrete dispatch target value, or nullopt.
static std::optional<uint64_t>
fwdInterpretTrial(llvm::Function &F, llvm::CallInst *DispatchCall,
                   const BinaryMemoryMap *BMM, uint64_t &RNG,
                   uint64_t AllocaBase) {
  const auto &DL = F.getDataLayout();

  llvm::DenseMap<llvm::Value *, uint64_t> Env;
  std::map<uint64_t, uint8_t> VirtMem;

  // Initialize arguments.
  Env[F.getArg(0)] =
      0x1000'0000'0000ULL | (mcXorshift64(RNG) & 0xFFFF'FFFFULL);
  uint64_t EntryPC = extractEntryVA(F.getName());
  Env[F.getArg(1)] = EntryPC ? EntryPC : mcXorshift64(RNG);
  if (F.arg_size() > 2)
    Env[F.getArg(2)] = mcXorshift64(RNG);

  // Assign unique base addresses to allocas.
  uint64_t AB = AllocaBase;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
        Env[AI] = AB;
        AB += 0x1'0000ULL;
      }

  llvm::BasicBlock *PrevBB = nullptr;
  llvm::BasicBlock *CurBB = &F.getEntryBlock();
  constexpr unsigned MaxSteps = 100000;
  unsigned Steps = 0;

  while (CurBB && Steps < MaxSteps) {
    llvm::BasicBlock *NextBB = nullptr;

    for (auto &I : *CurBB) {
      if (++Steps > MaxSteps)
        return std::nullopt;

      // PHI: pick incoming value from PrevBB.
      if (auto *PHI = llvm::dyn_cast<llvm::PHINode>(&I)) {
        if (PrevBB) {
          int Idx = PHI->getBasicBlockIndex(PrevBB);
          Env[PHI] = (Idx >= 0)
                         ? fwdGetVal(PHI->getIncomingValue(Idx), Env, RNG)
                         : mcXorshift64(RNG);
        } else {
          Env[PHI] = mcXorshift64(RNG);
        }
        continue;
      }

      // Target dispatch call — return its target operand.
      if (&I == DispatchCall)
        return fwdGetVal(DispatchCall->getArgOperand(1), Env, RNG);

      // Binary operators.
      if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(&I)) {
        uint64_t L = fwdGetVal(BO->getOperand(0), Env, RNG);
        uint64_t R = fwdGetVal(BO->getOperand(1), Env, RNG);
        uint64_t Res;
        switch (BO->getOpcode()) {
        case llvm::Instruction::Add:  Res = L + R; break;
        case llvm::Instruction::Sub:  Res = L - R; break;
        case llvm::Instruction::Mul:  Res = L * R; break;
        case llvm::Instruction::Xor:  Res = L ^ R; break;
        case llvm::Instruction::And:  Res = L & R; break;
        case llvm::Instruction::Or:   Res = L | R; break;
        case llvm::Instruction::Shl:  Res = L << (R & 63); break;
        case llvm::Instruction::LShr: Res = L >> (R & 63); break;
        case llvm::Instruction::AShr:
          Res = uint64_t(int64_t(L) >> (R & 63)); break;
        case llvm::Instruction::UDiv: Res = R ? L / R : 0; break;
        case llvm::Instruction::URem: Res = R ? L % R : 0; break;
        case llvm::Instruction::SDiv:
          Res = R ? uint64_t(int64_t(L) / int64_t(R)) : 0; break;
        case llvm::Instruction::SRem:
          Res = R ? uint64_t(int64_t(L) % int64_t(R)) : 0; break;
        default: Res = mcXorshift64(RNG); break;
        }
        Env[&I] = Res;
        continue;
      }

      // Cast instructions.
      if (auto *Cast = llvm::dyn_cast<llvm::CastInst>(&I)) {
        uint64_t Op = fwdGetVal(Cast->getOperand(0), Env, RNG);
        unsigned SrcBits = Cast->getSrcTy()->getScalarSizeInBits();
        unsigned DstBits = Cast->getDestTy()->getScalarSizeInBits();
        uint64_t Res;
        switch (Cast->getOpcode()) {
        case llvm::Instruction::ZExt:
          Res = (SrcBits < 64) ? (Op & ((1ULL << SrcBits) - 1)) : Op; break;
        case llvm::Instruction::SExt: {
          uint64_t V = (SrcBits < 64) ? (Op & ((1ULL << SrcBits) - 1)) : Op;
          if (SrcBits < 64 && (V & (1ULL << (SrcBits - 1))))
            V |= ~((1ULL << SrcBits) - 1);
          Res = V;
          break;
        }
        case llvm::Instruction::Trunc:
          Res = (DstBits < 64) ? (Op & ((1ULL << DstBits) - 1)) : Op; break;
        case llvm::Instruction::IntToPtr:
        case llvm::Instruction::PtrToInt:
        case llvm::Instruction::BitCast:
          Res = Op; break;
        default: Res = mcXorshift64(RNG); break;
        }
        Env[&I] = Res;
        continue;
      }

      // ICmp.
      if (auto *IC = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        uint64_t L = fwdGetVal(IC->getOperand(0), Env, RNG);
        uint64_t R = fwdGetVal(IC->getOperand(1), Env, RNG);
        bool Res = false;
        switch (IC->getPredicate()) {
        case llvm::ICmpInst::ICMP_EQ:  Res = L == R; break;
        case llvm::ICmpInst::ICMP_NE:  Res = L != R; break;
        case llvm::ICmpInst::ICMP_UGT: Res = L > R; break;
        case llvm::ICmpInst::ICMP_UGE: Res = L >= R; break;
        case llvm::ICmpInst::ICMP_ULT: Res = L < R; break;
        case llvm::ICmpInst::ICMP_ULE: Res = L <= R; break;
        case llvm::ICmpInst::ICMP_SGT:
          Res = int64_t(L) > int64_t(R); break;
        case llvm::ICmpInst::ICMP_SGE:
          Res = int64_t(L) >= int64_t(R); break;
        case llvm::ICmpInst::ICMP_SLT:
          Res = int64_t(L) < int64_t(R); break;
        case llvm::ICmpInst::ICMP_SLE:
          Res = int64_t(L) <= int64_t(R); break;
        default: break;
        }
        Env[&I] = Res ? 1ULL : 0ULL;
        continue;
      }

      // Select.
      if (auto *Sel = llvm::dyn_cast<llvm::SelectInst>(&I)) {
        uint64_t Cond = fwdGetVal(Sel->getCondition(), Env, RNG);
        Env[&I] = fwdGetVal(
            (Cond & 1) ? Sel->getTrueValue() : Sel->getFalseValue(),
            Env, RNG);
        continue;
      }

      // GEP.
      if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(&I)) {
        uint64_t Base = fwdGetVal(GEP->getPointerOperand(), Env, RNG);
        llvm::APInt Off(64, 0);
        if (GEP->accumulateConstantOffset(DL, Off)) {
          Env[&I] = Base + Off.getZExtValue();
        } else if (GEP->getSourceElementType()->isIntegerTy(8) &&
                   GEP->getNumIndices() == 1) {
          Env[&I] = Base + fwdGetVal(GEP->getOperand(1), Env, RNG);
        } else {
          Env[&I] = mcXorshift64(RNG);
        }
        continue;
      }

      // Load.
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        uint64_t Addr = fwdGetVal(LI->getPointerOperand(), Env, RNG);
        unsigned Bytes = DL.getTypeStoreSize(LI->getType());
        if (Bytes > 0 && Bytes <= 8) {
          auto Val = virtMemLoad(VirtMem, Addr, Bytes);
          if (!Val && BMM) {
            uint8_t Buf[8] = {};
            if (BMM->read(Addr, Buf, Bytes)) {
              uint64_t V = 0;
              for (unsigned i = 0; i < Bytes; ++i)
                V |= uint64_t(Buf[i]) << (i * 8);
              Val = V;
            }
          }
          Env[&I] = Val.value_or(mcXorshift64(RNG));
        } else {
          Env[&I] = mcXorshift64(RNG);
        }
        continue;
      }

      // Store.
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        uint64_t Addr = fwdGetVal(SI->getPointerOperand(), Env, RNG);
        uint64_t Val = fwdGetVal(SI->getValueOperand(), Env, RNG);
        unsigned Bytes = DL.getTypeStoreSize(SI->getValueOperand()->getType());
        if (Bytes > 0 && Bytes <= 8)
          virtMemStore(VirtMem, Addr, Val, Bytes);
        continue;
      }

      // Branch.
      if (auto *BI = llvm::dyn_cast<llvm::BranchInst>(&I)) {
        if (BI->isUnconditional()) {
          NextBB = BI->getSuccessor(0);
        } else {
          uint64_t Cond = fwdGetVal(BI->getCondition(), Env, RNG);
          NextBB = (Cond & 1) ? BI->getSuccessor(0) : BI->getSuccessor(1);
        }
        break;
      }

      // Switch.
      if (auto *SW = llvm::dyn_cast<llvm::SwitchInst>(&I)) {
        uint64_t Cond = fwdGetVal(SW->getCondition(), Env, RNG);
        NextBB = SW->getDefaultDest();
        for (auto &Case : SW->cases()) {
          if (Case.getCaseValue()->getZExtValue() == Cond) {
            NextBB = Case.getCaseSuccessor();
            break;
          }
        }
        break;
      }

      // Return / Unreachable: dispatch call not reached on this path.
      if (llvm::isa<llvm::ReturnInst>(&I) ||
          llvm::isa<llvm::UnreachableInst>(&I))
        return std::nullopt;

      // Call instructions.
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        if (auto *Callee = CI->getCalledFunction()) {
          auto IID = Callee->getIntrinsicID();
          if (IID == llvm::Intrinsic::ctpop) {
            uint64_t Op = fwdGetVal(CI->getArgOperand(0), Env, RNG);
            unsigned Bits = CI->getType()->getIntegerBitWidth();
            uint64_t Mask =
                (Bits < 64) ? ((1ULL << Bits) - 1) : ~0ULL;
            uint64_t V = Op & Mask;
            unsigned Count = 0;
            while (V) { V &= V - 1; ++Count; }
            Env[&I] = Count;
            continue;
          }
          if (IID == llvm::Intrinsic::umax) {
            Env[&I] = std::max(fwdGetVal(CI->getArgOperand(0), Env, RNG),
                               fwdGetVal(CI->getArgOperand(1), Env, RNG));
            continue;
          }
          if (IID == llvm::Intrinsic::umin) {
            Env[&I] = std::min(fwdGetVal(CI->getArgOperand(0), Env, RNG),
                               fwdGetVal(CI->getArgOperand(1), Env, RNG));
            continue;
          }
          if (IID == llvm::Intrinsic::bswap) {
            uint64_t Op = fwdGetVal(CI->getArgOperand(0), Env, RNG);
            unsigned Bits = CI->getType()->getIntegerBitWidth();
            unsigned NBytes = Bits / 8;
            uint64_t Res = 0;
            for (unsigned i = 0; i < NBytes; ++i)
              Res |= ((Op >> (i * 8)) & 0xFF) << ((NBytes - 1 - i) * 8);
            Env[&I] = Res;
            continue;
          }
          if (IID == llvm::Intrinsic::abs) {
            int64_t Op = int64_t(fwdGetVal(CI->getArgOperand(0), Env, RNG));
            Env[&I] = uint64_t(Op < 0 ? -Op : Op);
            continue;
          }
          // doesNotAccessMemory intrinsics produce unknown values.
          if (Callee->doesNotAccessMemory() ||
              Callee->getName().starts_with("__remill_undefined_")) {
            if (!CI->getType()->isVoidTy())
              Env[&I] = mcXorshift64(RNG);
            continue;
          }
        }
        // Other calls: random result, but they may write memory.
        // For safety, don't invalidate VirtMem (the dispatch chain
        // typically has no aliasing calls).
        if (!CI->getType()->isVoidTy())
          Env[&I] = mcXorshift64(RNG);
        continue;
      }

      // ExtractElement: handle <2 x float> → float extraction.
      if (auto *EE = llvm::dyn_cast<llvm::ExtractElementInst>(&I)) {
        uint64_t Vec = fwdGetVal(EE->getVectorOperand(), Env, RNG);
        if (auto *IdxC =
                llvm::dyn_cast<llvm::ConstantInt>(EE->getIndexOperand())) {
          unsigned Idx = IdxC->getZExtValue();
          if (auto *VTy = llvm::dyn_cast<llvm::FixedVectorType>(
                  EE->getVectorOperand()->getType())) {
            unsigned EBits = VTy->getElementType()->getScalarSizeInBits();
            if (EBits <= 64 && Idx * EBits < 64) {
              uint64_t Mask =
                  (EBits < 64) ? ((1ULL << EBits) - 1) : ~0ULL;
              Env[&I] = (Vec >> (Idx * EBits)) & Mask;
              continue;
            }
          }
        }
        Env[&I] = mcXorshift64(RNG);
        continue;
      }

      // InsertElement.
      if (auto *IE = llvm::dyn_cast<llvm::InsertElementInst>(&I)) {
        uint64_t Vec = fwdGetVal(IE->getOperand(0), Env, RNG);
        uint64_t Elem = fwdGetVal(IE->getOperand(1), Env, RNG);
        if (auto *IdxC =
                llvm::dyn_cast<llvm::ConstantInt>(IE->getOperand(2))) {
          unsigned Idx = IdxC->getZExtValue();
          if (auto *VTy =
                  llvm::dyn_cast<llvm::FixedVectorType>(IE->getType())) {
            unsigned EBits = VTy->getElementType()->getScalarSizeInBits();
            if (EBits <= 64 && Idx * EBits < 64) {
              uint64_t Mask =
                  (EBits < 64) ? ((1ULL << EBits) - 1) : ~0ULL;
              Vec &= ~(Mask << (Idx * EBits));
              Vec |= (Elem & Mask) << (Idx * EBits);
              Env[&I] = Vec;
              continue;
            }
          }
        }
        Env[&I] = mcXorshift64(RNG);
        continue;
      }

      // Freeze: pass through.
      if (auto *FI = llvm::dyn_cast<llvm::FreezeInst>(&I)) {
        Env[&I] = fwdGetVal(FI->getOperand(0), Env, RNG);
        continue;
      }

      // Any other instruction that produces a value: random.
      if (!I.getType()->isVoidTy())
        Env[&I] = mcXorshift64(RNG);
    }

    PrevBB = CurBB;
    CurBB = NextBB;
  }

  return std::nullopt;
}

/// Try to resolve a dispatch target using forward Monte Carlo interpretation.
/// Walks the function forward from entry, tracking stores/loads through
/// virtual memory.  Handles cross-BB inttoptr store forwarding that the
/// backward MC evaluator cannot.
static std::optional<uint64_t>
tryForwardMonteCarloResolve(llvm::CallInst *DispatchCall,
                             llvm::Function &F,
                             const BinaryMemoryMap *BMM) {
  constexpr unsigned NumTrials = 32;
  constexpr uint64_t AllocaBase1 = 0x7FFE'0000'0000ULL;

  llvm::DenseMap<uint64_t, unsigned> Freq;
  for (unsigned Trial = 0; Trial < NumTrials; ++Trial) {
    uint64_t RNG = 0xCAFE'BABE'DEAD'BEEFULL ^
                   (uint64_t(Trial) * 0x9E37'79B9'7F4A'7C15ULL);
    auto Res = fwdInterpretTrial(F, DispatchCall, BMM, RNG, AllocaBase1);
    if (!Res)
      return std::nullopt;
    Freq[*Res]++;
  }

  uint64_t Candidate = 0;
  if (Freq.size() == 1) {
    Candidate = Freq.begin()->first;
  } else if (Freq.size() == 2 && BMM) {
    // Two-value split: integrity check branch.  Pick the valid address.
    auto It = Freq.begin();
    uint64_t ValA = It->first;
    unsigned CountA = It->second;
    ++It;
    uint64_t ValB = It->first;
    unsigned CountB = It->second;

    uint8_t ByteA = 0, ByteB = 0;
    bool ValidA = BMM->read(ValA, &ByteA, 1);
    bool ValidB = BMM->read(ValB, &ByteB, 1);
    if (ValidA && !ValidB)
      Candidate = ValA;
    else if (ValidB && !ValidA)
      Candidate = ValB;
    else if (ValidA && ValidB)
      Candidate = (CountA >= CountB) ? ValA : ValB;
    else
      return std::nullopt;
  } else {
    return std::nullopt;
  }

  // Cross-check: verify result is NOT alloca-dependent.
  constexpr uint64_t AllocaBase2 = 0x7FFF'0000'0000ULL;
  {
    uint64_t RNG = 0xCAFE'BABE'DEAD'BEEFULL;  // Same seed as trial 0.
    auto Res = fwdInterpretTrial(F, DispatchCall, BMM, RNG, AllocaBase2);
    if (!Res)
      return std::nullopt;
    if (Freq.size() == 1 && *Res != Candidate)
      return std::nullopt;
    if (Freq.size() == 2 && Freq.find(*Res) == Freq.end())
      return std::nullopt;
  }

  // Validate: candidate should be a valid binary address.
  if (BMM) {
    uint8_t Byte = 0;
    if (!BMM->read(Candidate, &Byte, 1))
      return std::nullopt;
  }

  return Candidate;
}

/// Check if a dispatch target is already resolved (ptrtoint of a Function).
bool isAlreadyResolved(llvm::Value *target) {
  if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target))
    if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
      return true;
  if (llvm::isa<llvm::ConstantInt>(target))
    return true;
  return false;
}

/// Resolve a dispatch_call target: replace with constant or ptrtoint(@import).
/// Returns true if the call was modified.
bool resolveDispatchCall(llvm::CallInst *call, uint64_t resolved_pc,
                         const BinaryMemoryMap *map,
                         const LiftedFunctionMap *lifted) {
  auto &M = *call->getFunction()->getParent();
  auto &Ctx = call->getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Priority 1: IAT import.
  if (map && map->hasImports()) {
    if (auto *imp = map->lookupImport(resolved_pc)) {
      auto *fn_type = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
      auto fn_callee = M.getOrInsertFunction(imp->function, fn_type);
      auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
      if (fn) {
        fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
        llvm::IRBuilder<> Builder(call);
        auto *fn_addr = Builder.CreatePtrToInt(fn, i64_ty,
                                               imp->function + ".addr");
        call->setArgOperand(1, fn_addr);
        return true;
      }
    }
  }

  // Priority 2: Direct call to lifted function.
  auto *target_fn = lifted ? lifted->lookup(resolved_pc) : nullptr;
  if (target_fn) {
    llvm::IRBuilder<> Builder(call);
    auto *direct_call = Builder.CreateCall(
        target_fn,
        {call->getArgOperand(0),
         llvm::ConstantInt::get(i64_ty, resolved_pc),
         call->getArgOperand(2)});
    call->replaceAllUsesWith(direct_call);
    call->eraseFromParent();
    return true;
  }

  // Priority 3: Replace target with constant (for downstream passes to handle).
  call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
  return true;
}

/// Resolve a dispatch_jump target.
/// Returns true if the call was modified.
bool resolveDispatchJump(llvm::CallInst *call, uint64_t resolved_pc,
                         const LiftedFunctionMap *lifted) {
  auto *F = call->getFunction();

  // Find the ret following the dispatch call, skipping intermediate
  // instructions (insertvalue chains from struct returns, etc.).
  llvm::ReturnInst *ret = nullptr;
  for (auto *N = call->getNextNode(); N; N = N->getNextNode()) {
    if (auto *R = llvm::dyn_cast<llvm::ReturnInst>(N)) {
      ret = R;
      break;
    }
    // Stop at terminators or side-effectful instructions.
    if (N->isTerminator() || N->mayHaveSideEffects())
      break;
  }
  if (!ret)
    return false;

  auto *BB = call->getParent();
  llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

  // Priority 1: Intra-function branch.
  if (auto *target_bb = findBlockForPC(*F, resolved_pc)) {
    llvm::IRBuilder<> Builder(call);
    auto *br = Builder.CreateBr(target_bb);

    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    ret->eraseFromParent();
    call->eraseFromParent();

    // Clean dead instructions between branch and end of block.
    while (&BB->back() != br) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
        successors(BB).begin(), successors(BB).end());
    for (auto *old_succ : old_succs)
      if (!new_succs.count(old_succ))
        old_succ->removePredecessor(BB);

    return true;
  }

  // Priority 2: Inter-function musttail call.
  auto *target_fn = lifted ? lifted->lookup(resolved_pc) : nullptr;
  if (target_fn) {
    auto &Ctx = F->getContext();
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

    llvm::IRBuilder<> Builder(call);
    auto *tail_call = Builder.CreateCall(
        target_fn,
        {call->getArgOperand(0),
         llvm::ConstantInt::get(i64_ty, resolved_pc),
         call->getArgOperand(2)});
    tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    auto *new_ret = Builder.CreateRet(tail_call);

    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    ret->eraseFromParent();
    call->eraseFromParent();

    while (&BB->back() != new_ret) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
        successors(BB).begin(), successors(BB).end());
    for (auto *old_succ : old_succs)
      if (!new_succs.count(old_succ))
        old_succ->removePredecessor(BB);

    return true;
  }

  // Priority 3: Replace target with constant for downstream passes.
  // For jumps, only accept if there's a trace-lift callback that can
  // discover the target — otherwise an MC-mispredicted constant would
  // be lowered to inttoptr(wrong_addr) with no recovery path.
  auto *i64_ty = llvm::Type::getInt64Ty(call->getContext());
  call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
  return true;
}

}  // namespace

llvm::PreservedAnalyses IndirectCallResolverPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map)
    return llvm::PreservedAnalyses::all();

  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());

  // Collect candidates: dispatch_call and dispatch_jump with non-constant,
  // non-resolved targets.  Count instructions for forward MC budget.
  struct Candidate {
    llvm::WeakTrackingVH call;
    bool is_jump;
  };
  llvm::SmallVector<Candidate, 8> candidates;
  unsigned inst_count = 0;

  for (auto &BB : F) {
    for (auto &I : BB) {
      ++inst_count;
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;
      if (call->arg_size() < 3)
        continue;

      bool is_call = (callee->getName() == "__omill_dispatch_call");
      bool is_jump = (callee->getName() == "__omill_dispatch_jump");
      if (!is_call && !is_jump)
        continue;

      auto *target = call->getArgOperand(1);
      if (isAlreadyResolved(target))
        continue;

      candidates.push_back({llvm::WeakTrackingVH(call), is_jump});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  // For very large functions (>10K instructions), skip Monte Carlo
  // resolution entirely.  The deterministic evaluator is fast (SSA walk
  // bounded by visited set), but backward MC builds a store map across
  // the entire function and runs 32+ trials with per-trial backward
  // walks through potentially huge basic blocks.  On 80K+ instruction
  // VM functions this takes minutes.  Constant targets in large functions
  // should already be folded by GVN/ConstantMemoryFolding.
  constexpr unsigned kBackwardMCInstLimit = 10000;
  bool skip_mc = (inst_count > kBackwardMCInstLimit);

  // Build the MC store map once. Entries use WeakTrackingVH so erasing
  // instructions during dispatch rewrites nulls stale references safely.
  const llvm::DataLayout &DL = F.getDataLayout();
  MCStoreMap SSM;
  if (!skip_mc)
    SSM = buildMCStoreMap(F, DL);

  bool changed = false;

  for (auto &cand : candidates) {
    auto *call = llvm::dyn_cast_or_null<llvm::CallInst>(cand.call);
    if (!call || !call->getParent() || call->arg_size() < 3)
      continue;

    auto *target = call->getArgOperand(1);
    auto resolved = evaluateToConstant(target, *map);
    // Monte Carlo fallback: if the deterministic evaluator fails (e.g., VM
    // handler MBA with symbolic operands that cancel out), try concrete
    // evaluation with random values for unknowns.
    if (!resolved && !skip_mc)
      resolved = tryMonteCarloResolve(target, F, map, &SSM);
    // Forward MC fallback: if backward MC fails (cross-BB inttoptr stores
    // that the backward evaluator can't forward), walk the function
    // forward, tracking stores/loads through virtual memory.
    // Skip for non-trivial functions — forward MC walks the entire
    // function per trial (33 trials per candidate), which is
    // O(candidates * 33 * MaxSteps) and prohibitively slow on inlined
    // VM handler chains.  Limit to small functions where cross-BB
    // store forwarding is the only reasonable resolution path.
    constexpr unsigned kForwardMCInstLimit = 1000;
    bool from_fwd_mc = false;
    if (!resolved && inst_count <= kForwardMCInstLimit) {
      resolved = tryForwardMonteCarloResolve(call, F, map);
      from_fwd_mc = resolved.has_value();
    }
    if (!resolved)
      continue;

    // Forward MC results are less reliable than deterministic evaluation
    // or backward MC — they can give wrong-but-consistent results when
    // they mismodel an instruction.  Only accept forward MC results that
    // resolve to a *known* destination (lifted function, intra-function
    // block, or IAT import).  Unknown targets are skipped — the main
    // pipeline's standard passes (GVN/InstCombine) may fold the MBA
    // correctly in a later phase.
    if (from_fwd_mc) {
      uint64_t rpc = *resolved;
      bool known = false;
      if (lifted && lifted->lookup(rpc))
        known = true;
      if (!known && findBlockForPC(F, rpc))
        known = true;
      if (!known && map && map->hasImports() && map->lookupImport(rpc))
        known = true;
      if (!known)
        continue;
    }

    if (cand.is_jump) {
      changed |= resolveDispatchJump(call, *resolved, lifted);
    } else {
      changed |= resolveDispatchCall(call, *resolved, map, lifted);
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
