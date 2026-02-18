#include "omill/Passes/ResolveAndLowerControlFlow.h"

#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/KnownBits.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

#include "JumpTableUtils.h"

namespace omill {

namespace {

// ===----------------------------------------------------------------------===
// Phase 1: ResolveTargets — resolve constant-PC dispatch calls/jumps
// ===----------------------------------------------------------------------===

bool isAlreadyResolved(llvm::Value *target) {
  if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target))
    if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
      return true;
  return false;
}

bool resolveDispatchTargets(llvm::Function &F,
                            const BinaryMemoryMap *map,
                            const LiftedFunctionMap *lifted) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  bool changed = false;

  // --- Resolve dispatch_call targets ---
  {
    llvm::SmallVector<llvm::CallInst *, 4> candidates;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->getName() != "__omill_dispatch_call")
          continue;
        if (call->arg_size() < 3)
          continue;

        auto *target = call->getArgOperand(1);
        if (isAlreadyResolved(target))
          continue;

        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(target);
        if (!ci)
          continue;

        candidates.push_back(call);
      }
    }

    for (auto *call : candidates) {
      auto *ci = llvm::cast<llvm::ConstantInt>(call->getArgOperand(1));
      uint64_t target_pc = ci->getZExtValue();

      // Priority 1: IAT import lookup.
      if (map && map->hasImports()) {
        if (auto *imp = map->lookupImport(target_pc)) {
          auto *fn_type =
              llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
          auto fn_callee = M.getOrInsertFunction(imp->function, fn_type);
          auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
          if (fn) {
            fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
            llvm::IRBuilder<> Builder(call);
            auto *fn_addr = Builder.CreatePtrToInt(fn, i64_ty,
                                                    imp->function + ".addr");
            call->setArgOperand(1, fn_addr);
            changed = true;
            continue;
          }
        }
      }

      // Priority 2: Direct call to lifted function.
      auto *target_fn = lifted ? lifted->lookup(target_pc) : nullptr;
      if (target_fn) {
        llvm::IRBuilder<> Builder(call);
        auto *direct_call = Builder.CreateCall(
            target_fn, {call->getArgOperand(0), ci, call->getArgOperand(2)});
        call->replaceAllUsesWith(direct_call);
        call->eraseFromParent();
        changed = true;
      }
    }
  }

  // --- Resolve dispatch_jump targets ---
  {
    struct JumpCandidate {
      llvm::CallInst *call;
      llvm::ReturnInst *ret;
      uint64_t target_pc;
    };
    llvm::SmallVector<JumpCandidate, 4> candidates;

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

        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!ci)
          continue;

        auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
        if (!ret)
          continue;

        candidates.push_back({call, ret, ci->getZExtValue()});
      }
    }

    for (auto &[call, ret, target_pc] : candidates) {
      auto *BB = call->getParent();
      llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

      // Priority 1: Intra-function branch.
      if (auto *target_bb = findBlockForPC(F, target_pc)) {
        llvm::IRBuilder<> Builder(call);
        auto *br = Builder.CreateBr(target_bb);

        call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
        ret->eraseFromParent();
        call->eraseFromParent();

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

        changed = true;
        continue;
      }

      // Priority 2: Inter-function tail call.
      auto *target_fn = lifted ? lifted->lookup(target_pc) : nullptr;
      if (target_fn) {
        llvm::IRBuilder<> Builder(call);
        auto *state = call->getArgOperand(0);
        auto *pc_val = call->getArgOperand(1);
        auto *mem = call->getArgOperand(2);

        auto *tail_call = Builder.CreateCall(target_fn, {state, pc_val, mem});
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

        changed = true;
      }
    }
  }

  return changed;
}

// ===----------------------------------------------------------------------===
// Phase 2: RecoverTables — pattern-match jump table loads
// ===----------------------------------------------------------------------===

struct JumpTableCandidate {
  llvm::CallInst *dispatch_call;
  llvm::ReturnInst *ret;
  llvm::LoadInst *table_load;
  jt::LinearAddress addr;
  uint64_t image_base;
  uint64_t num_entries;
};

bool recoverJumpTables(llvm::Function &F,
                       const BinaryMemoryMap *map,
                       const LiftedFunctionMap *lifted) {
  if (!map || map->empty())
    return false;

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

      // Skip already-constant targets (handled by ResolveTargets phase).
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      // Unwrap RVA conversion if present.
      auto [image_base, load_val] = jt::unwrapRVAConversion(target);

      // Strip zext/sext from load value.
      if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(load_val))
        load_val = zext->getOperand(0);
      else if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(load_val))
        load_val = sext->getOperand(0);

      auto *table_load = llvm::dyn_cast<llvm::LoadInst>(load_val);
      if (!table_load)
        continue;

      // Decompose load pointer into base + idx * stride.
      auto addr_info = jt::decomposeTableAddress(table_load->getPointerOperand());
      if (!addr_info)
        continue;

      // Find bounds.
      auto bound = jt::computeIndexRange(addr_info->index, call->getParent());
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
    return false;

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.addr;

    auto raw_entries = jt::readTableEntries(*map, addr.base, addr.stride,
                                            cand.num_entries);
    if (!raw_entries)
      continue;

    jt::applyRVAConversion(*raw_entries, cand.image_base, addr.stride);

    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.image_base, cand.dispatch_call,
        cand.ret, F, *map, lifted);

    if (result.changed)
      changed = true;
  }

  return changed;
}

// ===----------------------------------------------------------------------===
// Phase 3: SymbolicSolve — SCEV/KnownBits fallback for table index bounds
// ===----------------------------------------------------------------------===

std::optional<uint64_t> scevBound(llvm::ScalarEvolution &SE,
                                   llvm::Value *idx) {
  if (!SE.isSCEVable(idx->getType()))
    return std::nullopt;

  auto *scev = SE.getSCEV(idx);
  auto range = SE.getUnsignedRange(scev);
  if (range.isFullSet() || range.isEmptySet())
    return std::nullopt;

  auto upper = range.getUnsignedMax().getZExtValue();
  if (upper == 0 || upper > 1024)
    return std::nullopt;

  return upper + 1;  // exclusive
}

std::optional<uint64_t> knownBitsBound(const llvm::DataLayout &DL,
                                        llvm::Value *idx) {
  llvm::KnownBits KB = llvm::computeKnownBits(idx, DL);
  llvm::APInt max_val = ~KB.Zero;
  uint64_t upper = max_val.getZExtValue();
  if (upper == 0 || upper > 1024)
    return std::nullopt;
  return upper + 1;  // exclusive
}

struct TableAccess {
  llvm::LoadInst *load;
  jt::LinearAddress addr;
  uint64_t image_base;
};

std::optional<TableAccess> analyzeTarget(llvm::Value *target) {
  auto [image_base, load_val] = jt::unwrapRVAConversion(target);

  if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(load_val))
    load_val = zext->getOperand(0);
  else if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(load_val))
    load_val = sext->getOperand(0);

  auto *table_load = llvm::dyn_cast<llvm::LoadInst>(load_val);
  if (!table_load)
    return std::nullopt;

  auto addr_info = jt::decomposeTableAddress(table_load->getPointerOperand());
  if (!addr_info)
    return std::nullopt;

  return TableAccess{table_load, *addr_info, image_base};
}

bool symbolicJumpTableSolve(llvm::Function &F,
                             llvm::FunctionAnalysisManager &AM,
                             const BinaryMemoryMap *map,
                             const LiftedFunctionMap *lifted) {
  if (!map || map->empty())
    return false;

  auto &DL = F.getParent()->getDataLayout();

  llvm::ScalarEvolution *SE = nullptr;
  auto getSE = [&]() -> llvm::ScalarEvolution & {
    if (!SE)
      SE = &AM.getResult<llvm::ScalarEvolutionAnalysis>(F);
    return *SE;
  };

  struct Candidate {
    llvm::CallInst *dispatch_call;
    llvm::ReturnInst *ret;
    TableAccess access;
    uint64_t num_entries;
  };

  llvm::SmallVector<Candidate, 4> candidates;

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
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      auto access = analyzeTarget(target);
      if (!access)
        continue;

      auto *idx = access->addr.index;

      // Try multiple bounding strategies.
      std::optional<uint64_t> bound;

      // 1. Pattern-based.
      bound = jt::computeIndexRange(idx, call->getParent());

      // 2. SCEV-based.
      if (!bound) {
        auto scev_result = scevBound(getSE(), idx);
        if (scev_result)
          bound = scev_result;
      }

      // 3. KnownBits-based.
      if (!bound) {
        auto kb_result = knownBitsBound(DL, idx);
        if (kb_result)
          bound = kb_result;
      }

      if (!bound || *bound == 0 || *bound > 1024)
        continue;

      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      if (!ret)
        continue;

      candidates.push_back({call, ret, *access, *bound});
    }
  }

  if (candidates.empty())
    return false;

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.access.addr;

    auto raw_entries =
        jt::readTableEntries(*map, addr.base, addr.stride, cand.num_entries);
    if (!raw_entries)
      continue;

    jt::applyRVAConversion(*raw_entries, cand.access.image_base, addr.stride);

    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.access.image_base,
        cand.dispatch_call, cand.ret, F, *map, lifted);

    if (result.changed)
      changed = true;
  }

  return changed;
}

}  // namespace

// ===----------------------------------------------------------------------===
// Main pass entry point
// ===----------------------------------------------------------------------===

llvm::PreservedAnalyses ResolveAndLowerControlFlowPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());

  bool changed = false;

  // Phase 1: Resolve constant-PC targets.
  if (phases_ & ResolvePhases::ResolveTargets)
    changed |= resolveDispatchTargets(F, map, lifted);

  // Phase 2: Recover jump tables via pattern matching.
  if (phases_ & ResolvePhases::RecoverTables)
    changed |= recoverJumpTables(F, map, lifted);

  // Phase 3: Symbolic fallback for table index bounds.
  if (phases_ & ResolvePhases::SymbolicSolve)
    changed |= symbolicJumpTableSolve(F, AM, map, lifted);

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
