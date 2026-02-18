#include "omill/Utils/LiftedNames.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>

namespace {

constexpr unsigned kMaxEvalDepth = 32;
constexpr size_t kMaxValueSetSize = 128;

using PCValueSet = llvm::SmallVector<uint64_t, 8>;

void appendUnique(PCValueSet &dst, uint64_t v) {
  for (uint64_t cur : dst) {
    if (cur == v)
      return;
  }
  if (dst.size() < kMaxValueSetSize)
    dst.push_back(v);
}

void appendAllUnique(PCValueSet &dst, const PCValueSet &src) {
  for (uint64_t v : src)
    appendUnique(dst, v);
}

uint64_t truncToBits(uint64_t v, unsigned bits) {
  if (bits >= 64)
    return v;
  return v & ((1ULL << bits) - 1ULL);
}

uint64_t sextFromBits(uint64_t v, unsigned bits) {
  if (bits >= 64)
    return v;
  const uint64_t mask = (1ULL << bits) - 1ULL;
  const uint64_t sign = 1ULL << (bits - 1U);
  uint64_t w = v & mask;
  if (w & sign)
    w |= ~mask;
  return w;
}

bool evalConcretePCValues(
    llvm::Value *V, llvm::Argument *pc_arg, uint64_t entry_va,
    llvm::DenseMap<llvm::Value *, PCValueSet> &memo,
    llvm::SmallPtrSet<llvm::Value *, 32> &in_progress, unsigned depth,
    PCValueSet &out) {
  if (!V || depth > kMaxEvalDepth)
    return false;

  auto mit = memo.find(V);
  if (mit != memo.end()) {
    out = mit->second;
    return !out.empty();
  }

  if (in_progress.contains(V))
    return false;
  in_progress.insert(V);

  PCValueSet values;

  if (V == pc_arg) {
    appendUnique(values, entry_va);
  } else if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    if (CI->getValue().getActiveBits() <= 64)
      appendUnique(values, CI->getZExtValue());
  } else if (auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
      PCValueSet incoming;
      if (!evalConcretePCValues(PN->getIncomingValue(i), pc_arg, entry_va,
                                memo, in_progress, depth + 1, incoming))
        continue;
      appendAllUnique(values, incoming);
    }
  } else if (auto *SI = llvm::dyn_cast<llvm::SelectInst>(V)) {
    PCValueSet tv;
    if (evalConcretePCValues(SI->getTrueValue(), pc_arg, entry_va, memo,
                             in_progress, depth + 1, tv))
      appendAllUnique(values, tv);
    PCValueSet fv;
    if (evalConcretePCValues(SI->getFalseValue(), pc_arg, entry_va, memo,
                             in_progress, depth + 1, fv))
      appendAllUnique(values, fv);
  } else if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    PCValueSet lhs, rhs;
    if (evalConcretePCValues(BO->getOperand(0), pc_arg, entry_va, memo,
                             in_progress, depth + 1, lhs) &&
        evalConcretePCValues(BO->getOperand(1), pc_arg, entry_va, memo,
                             in_progress, depth + 1, rhs)) {
      for (uint64_t l : lhs) {
        for (uint64_t r : rhs) {
          if (BO->getOpcode() == llvm::Instruction::Add)
            appendUnique(values, l + r);
          else if (BO->getOpcode() == llvm::Instruction::Sub)
            appendUnique(values, l - r);
          if (values.size() >= kMaxValueSetSize)
            break;
        }
        if (values.size() >= kMaxValueSetSize)
          break;
      }
    }
  } else if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V)) {
    PCValueSet src;
    if (evalConcretePCValues(CI->getOperand(0), pc_arg, entry_va, memo,
                             in_progress, depth + 1, src)) {
      const unsigned src_bits =
          CI->getSrcTy()->isIntegerTy() ? CI->getSrcTy()->getIntegerBitWidth()
                                        : 64;
      const unsigned dst_bits =
          CI->getDestTy()->isIntegerTy() ? CI->getDestTy()->getIntegerBitWidth()
                                         : 64;
      for (uint64_t v : src) {
        uint64_t out_v = v;
        if (auto *T = llvm::dyn_cast<llvm::TruncInst>(CI)) {
          (void)T;
          out_v = truncToBits(v, dst_bits);
        } else if (auto *Z = llvm::dyn_cast<llvm::ZExtInst>(CI)) {
          (void)Z;
          out_v = truncToBits(v, src_bits);
        } else if (auto *S = llvm::dyn_cast<llvm::SExtInst>(CI)) {
          (void)S;
          out_v = sextFromBits(v, src_bits);
        }
        appendUnique(values, out_v);
      }
    }
  } else if (auto *FI = llvm::dyn_cast<llvm::FreezeInst>(V)) {
    PCValueSet src;
    if (evalConcretePCValues(FI->getOperand(0), pc_arg, entry_va, memo,
                             in_progress, depth + 1, src))
      appendAllUnique(values, src);
  }

  in_progress.erase(V);
  memo[V] = values;
  out = values;
  return !out.empty();
}

}  // namespace

namespace omill {

llvm::DenseMap<uint64_t, llvm::BasicBlock *> collectBlockPCMap(
    llvm::Function &F) {
  llvm::DenseMap<uint64_t, llvm::BasicBlock *> pc_to_bb;

  for (auto &BB : F) {
    if (uint64_t named_pc = extractBlockPC(BB.getName()); named_pc != 0)
      pc_to_bb.try_emplace(named_pc, &BB);
  }

  // Fallback: infer block PCs from NEXT_PC SSA values after CFG simplification
  // has destroyed original block_<pc> names.
  uint64_t entry_va = extractEntryVA(F.getName());
  if (!entry_va || F.arg_size() < 2)
    return pc_to_bb;

  auto *pc_arg = llvm::dyn_cast<llvm::Argument>(F.getArg(1));
  if (!pc_arg || !pc_arg->getType()->isIntegerTy(64))
    return pc_to_bb;

  llvm::DenseMap<llvm::Value *, PCValueSet> memo;
  llvm::SmallPtrSet<llvm::Value *, 32> in_progress;

  auto maybeAddPC = [&](uint64_t candidate, llvm::BasicBlock *BB) {
    // Heuristic guard: keep values in a reasonable window around the
    // function entry VA to avoid collecting unrelated integer phis.
    constexpr uint64_t kWindow = 0x200000ULL;
    if (candidate + kWindow < entry_va || candidate > entry_va + kWindow)
      return;
    pc_to_bb.try_emplace(candidate, BB);
  };

  auto addFromPhi = [&](llvm::PHINode *PN, llvm::BasicBlock *BB) {
    PCValueSet values;
    if (!evalConcretePCValues(PN, pc_arg, entry_va, memo, in_progress, 0,
                              values))
      return;
    if (values.size() > 64)
      return;
    for (uint64_t candidate : values)
      maybeAddPC(candidate, BB);
  };

  for (auto &BB : F) {
    llvm::SmallVector<llvm::PHINode *, 8> phis;
    for (auto &I : BB) {
      auto *PN = llvm::dyn_cast<llvm::PHINode>(&I);
      if (!PN)
        break;
      if (!PN->getType()->isIntegerTy(64))
        continue;
      phis.push_back(PN);
    }

    bool added_named = false;
    for (auto *PN : phis) {
      if (!PN->getName().contains_insensitive("next_pc"))
        continue;
      addFromPhi(PN, &BB);
      added_named = true;
    }

    // If names were stripped, fall back to all i64 phis in this block.
    if (!added_named) {
      for (auto *PN : phis)
        addFromPhi(PN, &BB);
    }
  }

  return pc_to_bb;
}

llvm::SmallVector<uint64_t, 8> collectPossiblePCValues(
    llvm::Value *V, llvm::Function &F, size_t max_values) {
  llvm::SmallVector<uint64_t, 8> result;

  uint64_t entry_va = extractEntryVA(F.getName());
  if (!entry_va || F.arg_size() < 2)
    return result;

  auto *pc_arg = llvm::dyn_cast<llvm::Argument>(F.getArg(1));
  if (!pc_arg || !pc_arg->getType()->isIntegerTy(64))
    return result;

  llvm::DenseMap<llvm::Value *, PCValueSet> memo;
  llvm::SmallPtrSet<llvm::Value *, 32> in_progress;
  PCValueSet values;
  if (!evalConcretePCValues(V, pc_arg, entry_va, memo, in_progress, 0, values))
    return result;

  for (uint64_t v : values) {
    result.push_back(v);
    if (result.size() >= max_values)
      break;
  }
  return result;
}

llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc) {
  auto pc_to_bb = collectBlockPCMap(F);
  auto it = pc_to_bb.find(pc);
  if (it != pc_to_bb.end())
    return it->second;

  return nullptr;
}

uint64_t extractEntryVA(llvm::StringRef name) {
  if (!name.starts_with("sub_"))
    return 0;
  llvm::StringRef hex = name.drop_front(4);
  auto dot = hex.find('.');
  if (dot != llvm::StringRef::npos)
    hex = hex.substr(0, dot);
  uint64_t va = 0;
  if (hex.getAsInteger(16, va))
    return 0;
  return va;
}

bool isLiftedFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.getName().starts_with("__remill_"))
    return false;
  if (F.getName().starts_with("__omill_"))
    return false;
  if (F.getName().ends_with("_native"))
    return false;

  // Structural check: (ptr, i64, ptr) -> ptr
  if (F.arg_size() != 3)
    return false;
  auto *FTy = F.getFunctionType();
  if (!FTy->getReturnType()->isPointerTy())
    return false;
  if (!FTy->getParamType(0)->isPointerTy())
    return false;
  if (!FTy->getParamType(1)->isIntegerTy(64))
    return false;
  if (!FTy->getParamType(2)->isPointerTy())
    return false;

  return true;
}

bool hasLiftedSignature(const llvm::Function &F) {
  if (F.arg_size() != 3)
    return false;
  auto *FTy = F.getFunctionType();
  if (!FTy->getReturnType()->isPointerTy())
    return false;
  if (!FTy->getParamType(0)->isPointerTy())
    return false;
  if (!FTy->getParamType(1)->isIntegerTy(64))
    return false;
  if (!FTy->getParamType(2)->isPointerTy())
    return false;
  return true;
}

uint64_t extractBlockPC(llvm::StringRef name) {
  if (!name.starts_with("block_"))
    return 0;

  llvm::StringRef rest = name.drop_front(6);
  size_t hex_len = 0;
  while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
    ++hex_len;
  if (hex_len == 0)
    return 0;

  llvm::StringRef hex = rest.substr(0, hex_len);
  uint64_t pc = 0;
  if (hex.getAsInteger(16, pc))
    return 0;
  return pc;
}

}  // namespace omill
