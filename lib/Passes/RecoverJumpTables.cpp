#include "omill/Passes/RecoverJumpTables.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PatternMatch.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

namespace {

using namespace llvm::PatternMatch;

struct LinearAddress {
  llvm::Value *index;    // The non-constant index variable.
  uint64_t base;         // Constant base address of the table.
  unsigned stride;       // Byte stride per entry (4 or 8).
};

/// Decompose a pointer operand into base + index * stride.
/// Handles patterns like:
///   inttoptr(add(shl(idx, 2), base_const))
///   inttoptr(add(mul(idx, 4), base_const))
///   inttoptr(add(idx, base_const))  — stride 1 (not useful, skip)
std::optional<LinearAddress> decomposeTableAddress(llvm::Value *ptr) {
  // Strip inttoptr.
  llvm::Value *addr = nullptr;
  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
    addr = ITP->getOperand(0);
  else
    return std::nullopt;

  // Match: add(scaled_idx, const_base) or add(const_base, scaled_idx)
  llvm::Value *lhs, *rhs;
  if (!match(addr, m_Add(m_Value(lhs), m_Value(rhs))))
    return std::nullopt;

  // One side should be a constant (the base), the other the scaled index.
  llvm::ConstantInt *base_ci = nullptr;
  llvm::Value *scaled = nullptr;

  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(rhs)) {
    base_ci = ci;
    scaled = lhs;
  } else if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(lhs)) {
    base_ci = ci;
    scaled = rhs;
  } else {
    return std::nullopt;
  }

  uint64_t base = base_ci->getZExtValue();

  // Try to decompose scaled into index * stride.
  // Pattern 1: shl(idx, shift) where stride = 1 << shift
  llvm::Value *idx;
  llvm::ConstantInt *shift_ci;
  if (match(scaled, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
    unsigned shift = shift_ci->getZExtValue();
    if (shift == 2 || shift == 3) {
      return LinearAddress{idx, base, 1u << shift};
    }
    return std::nullopt;
  }

  // Pattern 2: mul(idx, stride_const)
  llvm::ConstantInt *stride_ci;
  if (match(scaled, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
    uint64_t stride = stride_ci->getZExtValue();
    if (stride == 4 || stride == 8)
      return LinearAddress{idx, base, static_cast<unsigned>(stride)};
    return std::nullopt;
  }

  // Pattern 3: zext(shl(idx, shift)) or sext(shl(idx, shift))
  llvm::Value *inner;
  if (match(scaled, m_ZExt(m_Value(inner))) ||
      match(scaled, m_SExt(m_Value(inner)))) {
    if (match(inner, m_Shl(m_Value(idx), m_ConstantInt(shift_ci)))) {
      unsigned shift = shift_ci->getZExtValue();
      if (shift == 2 || shift == 3)
        return LinearAddress{idx, base, 1u << shift};
    }
    if (match(inner, m_Mul(m_Value(idx), m_ConstantInt(stride_ci)))) {
      uint64_t stride = stride_ci->getZExtValue();
      if (stride == 4 || stride == 8)
        return LinearAddress{idx, base, static_cast<unsigned>(stride)};
    }
  }

  return std::nullopt;
}

/// Find the upper bound on the index by searching for a dominating
/// icmp ult/ule %idx, N.
std::optional<uint64_t> findIndexBound(llvm::Value *idx,
                                        llvm::BasicBlock *dispatch_bb) {
  // Look for a conditional branch that guards the dispatch_bb.
  // Walk predecessors looking for: br(icmp ult/ule idx, N, dispatch_bb, default)
  for (auto *pred : predecessors(dispatch_bb)) {
    auto *BI = llvm::dyn_cast<llvm::BranchInst>(pred->getTerminator());
    if (!BI || !BI->isConditional())
      continue;

    auto *ICI = llvm::dyn_cast<llvm::ICmpInst>(BI->getCondition());
    if (!ICI)
      continue;

    auto pred_type = ICI->getPredicate();
    auto *lhs = ICI->getOperand(0);
    auto *rhs = ICI->getOperand(1);

    // icmp ult %idx, N — true successor is the switch path
    if (pred_type == llvm::ICmpInst::ICMP_ULT &&
        lhs == idx && BI->getSuccessor(0) == dispatch_bb) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs))
        return CI->getZExtValue();
    }

    // icmp uge %idx, N — false successor is the switch path
    if (pred_type == llvm::ICmpInst::ICMP_UGE &&
        lhs == idx && BI->getSuccessor(1) == dispatch_bb) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs))
        return CI->getZExtValue();
    }

    // icmp ule %idx, N — true successor is the switch path, bound = N + 1
    if (pred_type == llvm::ICmpInst::ICMP_ULE &&
        lhs == idx && BI->getSuccessor(0) == dispatch_bb) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs))
        return CI->getZExtValue() + 1;
    }

    // icmp ugt %idx, N — false successor is the switch path, bound = N + 1
    if (pred_type == llvm::ICmpInst::ICMP_UGT &&
        lhs == idx && BI->getSuccessor(1) == dispatch_bb) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs))
        return CI->getZExtValue() + 1;
    }
  }

  // Also check if idx itself is masked: idx = and(orig, mask)
  llvm::Value *orig;
  llvm::ConstantInt *mask_ci;
  if (match(idx, m_And(m_Value(orig), m_ConstantInt(mask_ci)))) {
    uint64_t mask = mask_ci->getZExtValue();
    // mask must be (2^n - 1) for a valid table size.
    if ((mask & (mask + 1)) == 0)
      return mask + 1;
  }

  return std::nullopt;
}

llvm::BasicBlock *findBlockForPC(llvm::Function &F, uint64_t pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "block_%llx", (unsigned long long)pc);
  for (auto &BB : F)
    if (BB.getName() == buf)
      return &BB;

  snprintf(buf, sizeof(buf), "block_%lx", (unsigned long)pc);
  for (auto &BB : F)
    if (BB.getName() == buf)
      return &BB;

  return nullptr;
}

llvm::Function *findLiftedFunction(llvm::Module &M, uint64_t target_pc) {
  char buf[64];
  snprintf(buf, sizeof(buf), "sub_%llx", (unsigned long long)target_pc);
  if (auto *F = M.getFunction(buf))
    return F;

  snprintf(buf, sizeof(buf), "sub_%lx", (unsigned long)target_pc);
  if (auto *F = M.getFunction(buf))
    return F;

  return nullptr;
}

struct JumpTableCandidate {
  llvm::CallInst *dispatch_call;
  llvm::ReturnInst *ret;
  llvm::LoadInst *table_load;
  LinearAddress addr;
  uint64_t image_base;  // Addend for RVA→VA conversion (0 for absolute).
  uint64_t num_entries;
};

/// Check if the target value has an add with a constant (RVA → VA conversion).
/// Returns the image_base addend and the load result.
std::pair<uint64_t, llvm::Value *> unwrapRVAConversion(llvm::Value *target) {
  llvm::Value *loaded;
  llvm::ConstantInt *addend;

  // target = add(zext(load_val), image_base)
  // or target = add(sext(load_val), image_base)
  // or target = add(load_val, image_base)
  if (match(target, m_Add(m_Value(loaded), m_ConstantInt(addend))))
    return {addend->getZExtValue(), loaded};
  if (match(target, m_Add(m_ConstantInt(addend), m_Value(loaded))))
    return {addend->getZExtValue(), loaded};

  return {0, target};
}

}  // namespace

llvm::PreservedAnalyses RecoverJumpTablesPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  auto &M = *F.getParent();
  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Collect candidates.
  llvm::SmallVector<JumpTableCandidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || callee->getName() != "__omill_dispatch_jump")
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *target = call->getArgOperand(1);

      // Skip already-constant targets (handled by ResolveDispatchTargets).
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      // Unwrap RVA conversion if present.
      auto [image_base, load_val] = unwrapRVAConversion(target);

      // Strip zext/sext from load value.
      if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(load_val))
        load_val = zext->getOperand(0);
      else if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(load_val))
        load_val = sext->getOperand(0);

      auto *table_load = llvm::dyn_cast<llvm::LoadInst>(load_val);
      if (!table_load)
        continue;

      // Decompose load pointer into base + idx * stride.
      auto addr_info = decomposeTableAddress(table_load->getPointerOperand());
      if (!addr_info)
        continue;

      // Find bounds.
      auto bound = findIndexBound(addr_info->index, call->getParent());
      if (!bound || *bound == 0 || *bound > 1024)
        continue;

      // Must be followed by ret.
      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      if (!ret)
        continue;

      candidates.push_back({call, ret, table_load, *addr_info,
                            image_base, *bound});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.addr;
    auto *BB = cand.dispatch_call->getParent();

    // Read table entries from binary memory.
    llvm::SmallVector<uint64_t, 16> entry_targets;
    bool all_readable = true;

    for (uint64_t i = 0; i < cand.num_entries; ++i) {
      uint64_t entry_addr = addr.base + i * addr.stride;
      auto val = map->readInt(entry_addr, addr.stride);
      if (!val) {
        all_readable = false;
        break;
      }

      uint64_t target_va = *val;
      // Apply RVA→VA conversion.
      if (cand.image_base != 0) {
        // For 4-byte entries, sign-extend from 32 bits for negative RVAs.
        if (addr.stride == 4)
          target_va = static_cast<uint64_t>(static_cast<int32_t>(*val));
        target_va += cand.image_base;
      }

      entry_targets.push_back(target_va);
    }

    if (!all_readable)
      continue;

    // Resolve each target to a block or function.
    struct CaseTarget {
      uint64_t index;
      llvm::BasicBlock *target_bb;
    };
    llvm::SmallVector<CaseTarget, 16> cases;
    llvm::BasicBlock *default_bb = nullptr;
    bool all_resolved = true;

    for (uint64_t i = 0; i < entry_targets.size(); ++i) {
      uint64_t target_va = entry_targets[i];

      // Try intra-function block.
      if (auto *target_bb = findBlockForPC(F, target_va)) {
        cases.push_back({i, target_bb});
        continue;
      }

      // Try inter-function tail call.
      if (auto *target_fn = findLiftedFunction(M, target_va)) {
        // Create a trampoline block with musttail call.
        char name[64];
        snprintf(name, sizeof(name), "jt_case_%llu",
                 (unsigned long long)i);
        auto *trampoline = llvm::BasicBlock::Create(Ctx, name, &F);
        llvm::IRBuilder<> TBuilder(trampoline);

        auto *state = cand.dispatch_call->getArgOperand(0);
        auto *pc_val = llvm::ConstantInt::get(i64_ty, target_va);
        auto *mem = cand.dispatch_call->getArgOperand(2);

        auto *tail = TBuilder.CreateCall(target_fn, {state, pc_val, mem});
        tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
        TBuilder.CreateRet(tail);

        cases.push_back({i, trampoline});
        continue;
      }

      // Unknown target — this entry goes to the default case.
      all_resolved = false;
    }

    // Create default block: keep original dispatch_jump for unknown targets.
    if (!all_resolved || cases.size() < entry_targets.size()) {
      // Default keeps the original dispatch_jump. We'll leave BB as-is for the
      // default path. Actually, we need to split: create a new default block.
      default_bb = llvm::BasicBlock::Create(Ctx, "jt_default", &F);
      llvm::IRBuilder<> DBuilder(default_bb);
      // Re-create the dispatch_jump + ret for the default case.
      auto *dispatch_fn = cand.dispatch_call->getCalledFunction();
      auto *new_call = DBuilder.CreateCall(
          dispatch_fn,
          {cand.dispatch_call->getArgOperand(0),
           cand.dispatch_call->getArgOperand(1),
           cand.dispatch_call->getArgOperand(2)});
      DBuilder.CreateRet(new_call);
    } else {
      // All resolved — default is unreachable.
      default_bb = llvm::BasicBlock::Create(Ctx, "jt_default", &F);
      new llvm::UnreachableInst(Ctx, default_bb);
    }

    // Save old successors for PHI cleanup.
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    // Build switch instruction.
    llvm::IRBuilder<> Builder(cand.dispatch_call);
    auto *sw = Builder.CreateSwitch(addr.index, default_bb,
                                     cases.size());
    for (auto &c : cases)
      sw->addCase(llvm::ConstantInt::get(
                      llvm::cast<llvm::IntegerType>(addr.index->getType()),
                      c.index),
                  c.target_bb);

    // Erase original dispatch_jump + ret + dead instructions.
    cand.dispatch_call->replaceAllUsesWith(
        llvm::PoisonValue::get(cand.dispatch_call->getType()));
    cand.ret->eraseFromParent();
    cand.dispatch_call->eraseFromParent();

    // Clean up dead instructions after switch.
    while (&BB->back() != sw) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Update PHI nodes for removed predecessors.
    llvm::SmallPtrSet<llvm::BasicBlock *, 16> new_succs(
        successors(BB).begin(), successors(BB).end());
    for (auto *old_succ : old_succs)
      if (!new_succs.count(old_succ))
        old_succ->removePredecessor(BB);

    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
