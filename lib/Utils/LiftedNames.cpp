#include "omill/Utils/LiftedNames.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/FormatVariadic.h>

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

  auto *pc_slot = [&]() -> llvm::Value * {
    for (auto &I : F.getEntryBlock()) {
      if (I.getName() == "PC")
        return &I;
    }
    return nullptr;
  }();

  auto sameStateOffset = [&](llvm::Value *A, llvm::Value *B) -> bool {
    if (A == B)
      return true;
    auto *arg0 = F.arg_empty() ? nullptr : F.getArg(0);
    if (!arg0)
      return false;

    auto *GA = llvm::dyn_cast<llvm::GetElementPtrInst>(A);
    auto *GB = llvm::dyn_cast<llvm::GetElementPtrInst>(B);
    if (!GA || !GB || GA->getPointerOperand() != arg0 ||
        GB->getPointerOperand() != arg0 || !GA->hasAllConstantIndices() ||
        !GB->hasAllConstantIndices())
      return false;

    llvm::APInt off_a(64, 0);
    llvm::APInt off_b(64, 0);
    if (!GA->accumulateConstantOffset(F.getDataLayout(), off_a) ||
        !GB->accumulateConstantOffset(F.getDataLayout(), off_b))
      return false;
    return off_a == off_b;
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

    if (pc_slot) {
      for (auto &I : BB) {
        auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
        if (!SI || !SI->getValueOperand()->getType()->isIntegerTy(64))
          continue;
        if (!sameStateOffset(SI->getPointerOperand(), pc_slot))
          continue;

        auto values = collectPossiblePCValues(SI->getValueOperand(), F, 32);
        for (uint64_t candidate : values)
          maybeAddPC(candidate, &BB);
      }
    }

    // Broad fallback: collect any concrete PC-derived i64 SSA values in the
    // block. This recovers internal trace block entry PCs after LLVM has
    // stripped block names and folded NEXT_PC values through ordinary adds.
    for (auto &I : BB) {
      if (!I.getType()->isIntegerTy(64))
        continue;
      auto values = collectPossiblePCValues(&I, F, 32);
      for (uint64_t candidate : values)
        maybeAddPC(candidate, &BB);
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

llvm::Function *findLiftedOrBlockFunctionByPC(llvm::Module &M, uint64_t pc) {
  for (llvm::StringRef prefix : {"sub_", "blk_", "block_"}) {
    std::string name = (prefix + llvm::Twine::utohexstr(pc)).str();
    if (auto *fn = M.getFunction(name); fn && !fn->isDeclaration())
      return fn;
  }
  return nullptr;
}

llvm::Function *findLiftedOrCoveredFunctionByPC(llvm::Module &M, uint64_t pc) {
  if (auto *exact = findLiftedOrBlockFunctionByPC(M, pc))
    return exact;

  for (auto &F : M) {
    if (F.isDeclaration() || !hasLiftedSignature(F))
      continue;
    if (extractEntryVA(F.getName()) == pc || extractBlockPC(F.getName()) == pc)
      return &F;
    auto pc_to_bb = collectBlockPCMap(F);
    if (pc_to_bb.find(pc) != pc_to_bb.end())
      return &F;
  }

  return nullptr;
}

llvm::Function *findStructuralCodeTargetFunctionByPC(llvm::Module &M,
                                                     uint64_t pc) {
  for (auto &F : M) {
    if (extractStructuralCodeTargetPC(F) == pc)
      return &F;
  }
  return nullptr;
}

std::optional<uint64_t> findNearestCoveredLiftedOrBlockPC(llvm::Module &M,
                                                          uint64_t pc,
                                                          uint64_t max_distance) {
  std::optional<uint64_t> best_pc;
  uint64_t best_distance = std::numeric_limits<uint64_t>::max();

  auto consider = [&](uint64_t candidate) {
    const uint64_t distance =
        candidate > pc ? candidate - pc : pc - candidate;
    if (distance > max_distance)
      return;
    if (!best_pc || distance < best_distance ||
        (distance == best_distance && candidate < *best_pc)) {
      best_pc = candidate;
      best_distance = distance;
    }
  };

  for (auto &F : M) {
    if (F.isDeclaration() || !hasLiftedSignature(F))
      continue;
    if (uint64_t entry_pc = extractEntryVA(F.getName()); entry_pc != 0)
      consider(entry_pc);
    if (uint64_t block_pc = extractBlockPC(F.getName()); block_pc != 0)
      consider(block_pc);
    for (const auto &[block_pc, BB] : collectBlockPCMap(F)) {
      (void)BB;
      consider(block_pc);
    }
  }

  return best_pc;
}

uint64_t extractEntryVA(llvm::StringRef name) {
  if (!name.starts_with("sub_"))
    return 0;
  llvm::StringRef rest = name.drop_front(4);
  size_t hex_len = 0;
  while (hex_len < rest.size() && llvm::isHexDigit(rest[hex_len]))
    ++hex_len;
  if (hex_len == 0)
    return 0;

  llvm::StringRef hex = rest.substr(0, hex_len);
  uint64_t va = 0;
  if (hex.getAsInteger(16, va))
    return 0;
  return va;
}

uint64_t extractStructuralCodeTargetPC(llvm::StringRef name) {
  auto parseWithPrefix = [&](llvm::StringRef prefix) -> uint64_t {
    if (!name.starts_with(prefix))
      return 0;
    llvm::StringRef rest = name.drop_front(prefix.size());
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
  };

  if (uint64_t pc = extractEntryVA(name))
    return pc;
  if (uint64_t pc = extractBlockPC(name))
    return pc;
  if (uint64_t pc = parseWithPrefix("omill_native_target_"))
    return pc;
  if (uint64_t pc = parseWithPrefix("omill_native_boundary_"))
    return pc;
  if (uint64_t pc = parseWithPrefix("omill_executable_target_"))
    return pc;
  if (uint64_t pc = parseWithPrefix("omill_vm_enter_target_"))
    return pc;
  return 0;
}

uint64_t extractStructuralCodeTargetPC(const llvm::Function &F) {
  auto parseHexAttr = [&](llvm::StringRef key) -> uint64_t {
    auto attr = F.getFnAttribute(key);
    if (!attr.isValid())
      return 0;
    auto text = attr.getValueAsString();
    if (text.consume_front("0x") || text.consume_front("0X")) {
    }
    uint64_t value = 0;
    if (text.getAsInteger(16, value))
      return 0;
    return value;
  };

  if (uint64_t pc = parseHexAttr("omill.native_direct_target_pc"))
    return pc;
  if (uint64_t pc = parseHexAttr("omill.virtual_exit_native_target_pc"))
    return pc;
  if (uint64_t pc = parseHexAttr("omill.executable_target_pc"))
    return pc;
  if (uint64_t pc = parseHexAttr("omill.vm_enter_target_pc"))
    return pc;
  if (uint64_t pc = parseHexAttr("omill.native_boundary_pc"))
    return pc;
  return extractStructuralCodeTargetPC(F.getName());
}

std::string liftedFunctionName(uint64_t va) {
  return "sub_" + llvm::utohexstr(va, true);
}

std::string demergedHandlerCloneName(uint64_t va, uint64_t incoming_hash) {
  return liftedFunctionName(va) + "__vm_" +
         llvm::utohexstr(incoming_hash, true);
}

llvm::StringRef canonicalDispatchIntrinsicName(
    DispatchIntrinsicKind kind, const llvm::Module &M) {
  if (prefersRawRemillDispatch(M)) {
    switch (kind) {
      case DispatchIntrinsicKind::kCall:
        return "__remill_function_call";
      case DispatchIntrinsicKind::kJump:
        return "__remill_jump";
    }
  }

  switch (kind) {
    case DispatchIntrinsicKind::kCall:
      return "__omill_dispatch_call";
    case DispatchIntrinsicKind::kJump:
      return "__omill_dispatch_jump";
  }
  return "__omill_dispatch_call";
}

bool prefersRawRemillDispatch(const llvm::Module &M) {
  auto *flag = M.getModuleFlag("omill.raw_remill_dispatch");
  if (!flag)
    return false;
  if (auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(flag))
    return ci->getZExtValue() != 0;
  return false;
}

bool isDispatchCallName(llvm::StringRef name) {
  return name == "__remill_function_call" ||
         name == "__omill_dispatch_call";
}

bool isDispatchJumpName(llvm::StringRef name) {
  return name == "__remill_jump" || name == "__omill_dispatch_jump";
}

bool isDispatchIntrinsicName(llvm::StringRef name) {
  return isDispatchCallName(name) || isDispatchJumpName(name);
}

bool isLegacyOmillDispatchName(llvm::StringRef name) {
  return name == "__omill_dispatch_call" || name == "__omill_dispatch_jump";
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
  llvm::StringRef rest;
  if (name.starts_with("block_")) {
    rest = name.drop_front(6);
  } else if (name.starts_with("blk_")) {
    rest = name.drop_front(4);
  } else {
    return 0;
  }
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

bool isClosedRootSliceScopedModule(const llvm::Module &M) {
  auto *flag = M.getModuleFlag("omill.closed_root_slice_scope");
  if (!flag)
    return false;
  if (auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(flag))
    return ci->getZExtValue() != 0;
  return false;
}

bool isClosedRootSliceFunction(const llvm::Function &F) {
  return F.hasFnAttribute("omill.closed_root_slice");
}

bool isClosedRootSliceRoot(const llvm::Function &F) {
  return F.hasFnAttribute("omill.closed_root_slice_root");
}

}  // namespace omill
