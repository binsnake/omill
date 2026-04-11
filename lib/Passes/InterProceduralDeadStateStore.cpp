#include "omill/Passes/InterProceduralDeadStateStore.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SparseBitVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <cstdlib>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

/// Local mirror of the scope predicate in Pipeline.cpp (which lives in an
/// anonymous namespace and therefore isn't externally linkable). Matches
/// the same rules: name prefixes, vm/newly-lifted attributes, or lifted
/// Remill signature without optnone.
bool hasLiftedRemillSignatureLocal(const llvm::Function &F) {
  auto *FT = F.getFunctionType();
  if (FT->getNumParams() != 3) return false;
  if (!FT->getReturnType()->isPointerTy()) return false;
  if (!FT->getParamType(0)->isPointerTy()) return false;
  if (!FT->getParamType(1)->isIntegerTy(64)) return false;
  if (!FT->getParamType(2)->isPointerTy()) return false;
  return true;
}

bool isLiftedPipelineFunctionLocal(const llvm::Function &F) {
  if (F.isDeclaration()) return false;

  auto name = F.getName();
  if (name.starts_with("sub_") || name.starts_with("block_") ||
      name.starts_with("blk_") || name.starts_with("__lifted_")) {
    return true;
  }

  if (F.hasFnAttribute("omill.vm_newly_lifted") ||
      F.hasFnAttribute("omill.newly_lifted") ||
      F.hasFnAttribute("omill.vm_handler") ||
      F.hasFnAttribute("omill.vm_wrapper") ||
      F.getFnAttribute("omill.vm_demerged_clone").isValid() ||
      F.getFnAttribute("omill.vm_outlined_virtual_call").isValid()) {
    return true;
  }

  return hasLiftedRemillSignatureLocal(F) &&
         !F.hasFnAttribute(llvm::Attribute::OptimizeNone);
}


/// Resolve a pointer value to its byte offset into the State struct.
/// Returns -1 if not resolvable to State. Copied verbatim from
/// InterProceduralConstProp.cpp (per plan).
int64_t resolveStateOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }
  return -1;
}

/// Lattice element: set of live State byte offsets (or "all").
struct LiveSet {
  bool all = false;
  llvm::SparseBitVector<> bytes;

  void setAll() {
    all = true;
    bytes.clear();
  }

  void markRange(unsigned off, unsigned size) {
    if (all) return;
    for (unsigned i = 0; i < size; ++i)
      bytes.set(off + i);
  }

  void clearRange(unsigned off, unsigned size) {
    if (all) return;  // "all" stays top; we never demote.
    for (unsigned i = 0; i < size; ++i)
      bytes.reset(off + i);
  }

  bool test(unsigned off, unsigned size) const {
    if (all) return true;
    for (unsigned i = 0; i < size; ++i)
      if (bytes.test(off + i))
        return true;
    return false;
  }

  /// live := live ∪ other. Returns true if live changed.
  bool unionWith(const LiveSet &other) {
    if (all) return false;
    if (other.all) {
      all = true;
      bytes.clear();
      return true;
    }
    return bytes |= other.bytes;
  }

  bool equals(const LiveSet &o) const {
    if (all != o.all) return false;
    if (all) return true;
    return bytes == o.bytes;
  }
};

/// Per-function transitive live-in closure.
struct PerFunctionInfo {
  LiveSet tli;
  bool tli_computed = false;
};

/// Classification of a pointer-typed call argument.
bool callHasStateDerivedArg(llvm::CallBase *CB, const llvm::DataLayout &DL) {
  for (unsigned i = 0, e = CB->arg_size(); i < e; ++i) {
    llvm::Value *arg = CB->getArgOperand(i);
    if (!arg->getType()->isPointerTy()) continue;
    if (resolveStateOffset(arg, DL) >= 0)
      return true;
  }
  return false;
}

/// Check if any argument beyond arg0 passes a non-zero State offset.
/// In that case we conservatively widen to all (interprocedural aliasing
/// via secondary args isn't modeled by TLI).
bool hasSecondaryStatePtrHazard(llvm::CallBase *CB,
                                const llvm::DataLayout &DL) {
  for (unsigned i = 1, e = CB->arg_size(); i < e; ++i) {
    llvm::Value *arg = CB->getArgOperand(i);
    if (!arg->getType()->isPointerTy()) continue;
    int64_t off = resolveStateOffset(arg, DL);
    if (off > 0) return true;
  }
  return false;
}

/// True for remill intrinsics that end the liftable slice with a runtime
/// handoff (no further lifted observation of State within this pipeline
/// run). Used in --no-abi mode where stores unused by lifted callees are
/// dead at the handoff boundary.
bool isRemillSliceExit(llvm::StringRef name) {
  return name == "__remill_missing_block" || name == "__remill_error" ||
         name == "__remill_function_return";
}

/// True for remill intrinsics that dispatch to another lifted function.
/// These are NOT slice exits — their callee reads State. When the target
/// PC is a constant and resolves via LiftedFunctionMap we can use the
/// resolved TLI; otherwise we widen to `all`.
bool isRemillDispatchLike(llvm::StringRef name) {
  return name == "__remill_jump" || name == "__remill_function_call";
}

/// Compute the contribution of a call site to the live set.
/// Given the already-computed TLI table (including current SCC estimates)
/// returns the set of State bytes that may be read by this call.
LiveSet computeCallContribution(
    llvm::CallInst *CI, const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Function *, PerFunctionInfo> &info,
    LiftedCallGraph &call_graph, LiftedFunctionMap &lifted_map) {
  LiveSet result;

  // Secondary-arg State pointer hazard → widen to all. Guards against
  // interprocedural aliasing through arg1/arg2 where the callee might
  // treat a non-arg0 argument as a State offset.
  if (hasSecondaryStatePtrHazard(CI, DL)) {
    result.setAll();
    return result;
  }

  llvm::Function *called = CI->getCalledFunction();

  // Indirect call without a resolvable callee.
  if (!called) {
    result.setAll();
    return result;
  }

  llvm::StringRef name = called->getName();

  // Slice-exit remill intrinsics (`__remill_missing_block` /
  // `__remill_error` / `__remill_function_return`) terminate the liftable
  // slice — the runtime adapter takes over and the omill pipeline stops
  // observing State here. In --no-abi mode this is the end of the
  // observation window.
  if (isRemillSliceExit(name)) {
    return result;
  }

  // `omill_native_boundary_*` placeholders are runtime handoffs to native
  // code, which operates on real machine registers rather than the lifted
  // State struct. Same reasoning as slice exits.
  if (name.starts_with("omill_native_boundary_")) {
    return result;
  }

  // LLVM intrinsics with memory(none) contribute nothing.
  if (called->isIntrinsic()) {
    if (called->doesNotAccessMemory())
      return result;
    // Other intrinsics (memcpy/memset/etc.): widen if any arg is
    // State-derived.
    if (callHasStateDerivedArg(CI, DL))
      result.setAll();
    return result;
  }

  // Direct call to a lifted function we've already analyzed (including
  // in-SCC forward edges during iterative fixpoint: in that case the
  // current estimate is a monotone under-approximation and we use it).
  auto it = info.find(called);
  if (it != info.end()) {
    return it->second.tli;
  }

  // Dispatch intrinsics (`__omill_dispatch_*` placeholders and remill
  // `__remill_jump` / `__remill_function_call`): the target PC is arg1.
  // If it resolves via LiftedFunctionMap we use the resolved callee's
  // TLI. Otherwise, treat the call as a terminal handoff (∅) consistent
  // with the slice-exit classification — in --no-abi mode the runtime
  // adapter ends the omill observation window at this point.
  if (name.starts_with("__omill_dispatch_") || isRemillDispatchLike(name)) {
    if (CI->arg_size() >= 2) {
      if (auto *target_ci =
              llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1))) {
        uint64_t pc = target_ci->getZExtValue();
        if (auto *target_fn = lifted_map.lookup(pc)) {
          auto jt = info.find(target_fn);
          if (jt != info.end())
            return jt->second.tli;
        }
      }
    }
    return result;
  }

  // External declaration (resolved by name but not in our lifted set).
  // If it takes no State-derived pointer arg it cannot read State —
  // contribute nothing. Otherwise, widen to all.
  if (called->isDeclaration()) {
    if (!callHasStateDerivedArg(CI, DL))
      return result;
    result.setAll();
    return result;
  }

  // Non-lifted definition with a body we haven't analyzed. Be
  // conservative about any call that passes State.
  if (!callHasStateDerivedArg(CI, DL))
    return result;
  result.setAll();
  return result;
}

/// Transform a block backward: given live_out, compute live_in.
/// Treats loads as generators, resolvable stores as full kills, and
/// calls as contribution unions (see computeCallContribution).
LiveSet transformBlock(
    llvm::BasicBlock &BB, const LiveSet &live_out,
    const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Function *, PerFunctionInfo> &info,
    LiftedCallGraph &call_graph, LiftedFunctionMap &lifted_map) {
  LiveSet live = live_out;

  for (auto it = BB.rbegin(), end = BB.rend(); it != end; ++it) {
    llvm::Instruction &I = *it;

    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      if (SI->isVolatile() || SI->isAtomic()) continue;
      int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
      if (off < 0) continue;  // pointer not State-derived: no effect
      unsigned size = static_cast<unsigned>(
          DL.getTypeStoreSize(SI->getValueOperand()->getType()));
      live.clearRange(static_cast<unsigned>(off), size);
      continue;
    }

    if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      if (LI->isVolatile() || LI->isAtomic()) continue;
      int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
      if (off < 0) continue;
      unsigned size =
          static_cast<unsigned>(DL.getTypeStoreSize(LI->getType()));
      live.markRange(static_cast<unsigned>(off), size);
      continue;
    }

    if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
      LiveSet contrib =
          computeCallContribution(CI, DL, info, call_graph, lifted_map);
      live.unionWith(contrib);
      continue;
    }
  }

  return live;
}

/// Compute TLI(F) by iterating a backward CFG dataflow until convergence.
/// Uses the current `info` table for call contributions (handles SCCs).
LiveSet computeFunctionTLI(
    llvm::Function &F, const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Function *, PerFunctionInfo> &info,
    LiftedCallGraph &call_graph, LiftedFunctionMap &lifted_map) {
  if (F.empty()) return {};

  llvm::DenseMap<llvm::BasicBlock *, LiveSet> block_live_in;

  // Simple iteration over blocks in function order. Lifted CFGs are
  // small (1–a few dozen blocks, usually acyclic), so a plain fixpoint
  // converges in ~2 rounds without needing a proper worklist.
  const unsigned kMaxRounds = 16;
  for (unsigned round = 0; round < kMaxRounds; ++round) {
    bool changed = false;
    for (auto &BB : F) {
      LiveSet live_out;
      for (auto *succ : llvm::successors(&BB)) {
        auto it = block_live_in.find(succ);
        if (it != block_live_in.end())
          live_out.unionWith(it->second);
      }
      LiveSet new_in =
          transformBlock(BB, live_out, DL, info, call_graph, lifted_map);
      auto &slot = block_live_in[&BB];
      if (!slot.equals(new_in)) {
        slot = std::move(new_in);
        changed = true;
      }
    }
    if (!changed) break;
  }

  auto entry_it = block_live_in.find(&F.getEntryBlock());
  if (entry_it == block_live_in.end()) return {};
  return entry_it->second;
}

/// Precomputed byte-level mask of offsets safe to consider for
/// elimination. A byte is "safe" if it lies inside a known GPR, flag,
/// or vector register's physical footprint. StateFieldMap overlays
/// register names via `__remill_basic_block`, where the GEPs are typed
/// as `i8` and therefore report `size = 1`. That's too narrow for a
/// byte-level safety mask: an 8-byte write to RAX at offset 2216 would
/// only see byte 2216 marked safe and fail the range check. We
/// compensate by expanding each field to its category's natural
/// physical width.
struct SafeOffsetMask {
  llvm::DenseSet<unsigned> bytes;

  explicit SafeOffsetMask(const StateFieldMap &fm) {
    auto addRange = [&](unsigned base, unsigned span) {
      for (unsigned i = 0; i < span; ++i)
        bytes.insert(base + i);
    };

    // GPRs: 8-byte physical width (x86-64 / AArch64).
    for (auto &f : fm.getGPRs()) {
      if (f.is_volatile_separator) continue;
      addRange(f.offset, 8);
    }
    // Flags: 1 byte each (remill encodes each flag as a separate i8
    // field).
    for (auto &f : fm.getFlags()) {
      if (f.is_volatile_separator) continue;
      addRange(f.offset, 1);
    }
    // Vector registers: conservative 16-byte window anchored at the
    // named field. YMM/ZMM upper halves on x86 live in adjacent fields
    // that will be marked independently.
    for (auto &f : fm.getVectorRegs()) {
      if (f.is_volatile_separator) continue;
      addRange(f.offset, 16);
    }
  }

  bool contains(unsigned off, unsigned size) const {
    for (unsigned i = 0; i < size; ++i)
      if (!bytes.count(off + i))
        return false;
    return true;
  }
};

/// Rewrite phase: eliminate dead stores in F using the computed TLIs.
/// Returns number of stores eliminated.
unsigned rewriteFunction(
    llvm::Function &F, const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Function *, PerFunctionInfo> &info,
    LiftedCallGraph &call_graph, LiftedFunctionMap &lifted_map,
    const SafeOffsetMask &safe_mask) {
  if (F.empty()) return 0;

  // Recompute per-block live_in using final TLIs.
  llvm::DenseMap<llvm::BasicBlock *, LiveSet> block_live_in;
  const unsigned kMaxRounds = 16;
  for (unsigned round = 0; round < kMaxRounds; ++round) {
    bool changed = false;
    for (auto &BB : F) {
      LiveSet live_out;
      for (auto *succ : llvm::successors(&BB)) {
        auto it = block_live_in.find(succ);
        if (it != block_live_in.end())
          live_out.unionWith(it->second);
      }
      LiveSet new_in =
          transformBlock(BB, live_out, DL, info, call_graph, lifted_map);
      auto &slot = block_live_in[&BB];
      if (!slot.equals(new_in)) {
        slot = std::move(new_in);
        changed = true;
      }
    }
    if (!changed) break;
  }

  llvm::SmallVector<llvm::StoreInst *, 16> to_erase;

  // Per-block backward rewrite.
  for (auto &BB : F) {
    LiveSet live;
    for (auto *succ : llvm::successors(&BB)) {
      auto it = block_live_in.find(succ);
      if (it != block_live_in.end())
        live.unionWith(it->second);
    }

    for (auto it = BB.rbegin(), end = BB.rend(); it != end; ++it) {
      llvm::Instruction &I = *it;

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        if (SI->isVolatile() || SI->isAtomic()) continue;
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off < 0) continue;
        unsigned size = static_cast<unsigned>(
            DL.getTypeStoreSize(SI->getValueOperand()->getType()));
        unsigned u_off = static_cast<unsigned>(off);

        bool safe_category = safe_mask.contains(u_off, size);

        if (safe_category && !live.test(u_off, size)) {
          to_erase.push_back(SI);
          // Don't update live — this store is being erased.
          continue;
        }
        // Store is live or not eliminable: it kills those bytes going
        // backward (for purposes of preceding stores).
        live.clearRange(u_off, size);
        continue;
      }

      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        if (LI->isVolatile() || LI->isAtomic()) continue;
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off < 0) continue;
        unsigned size =
            static_cast<unsigned>(DL.getTypeStoreSize(LI->getType()));
        live.markRange(static_cast<unsigned>(off), size);
        continue;
      }

      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        LiveSet contrib =
            computeCallContribution(CI, DL, info, call_graph, lifted_map);
        live.unionWith(contrib);
        continue;
      }
    }
  }

  for (auto *SI : to_erase) {
    SI->eraseFromParent();
  }
  return static_cast<unsigned>(to_erase.size());
}

bool envDisabledLocal(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0') return false;
  return (v[0] == '1' && v[1] == '\0') ||
         (v[0] == 't' && v[1] == '\0') ||
         (v[0] == 'T' && v[1] == '\0');
}

}  // namespace

llvm::PreservedAnalyses InterProceduralDeadStateStorePass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  if (envDisabledLocal("OMILL_SKIP_IPDSE"))
    return llvm::PreservedAnalyses::all();

  auto &call_graph = MAM.getResult<CallGraphAnalysis>(M);
  auto &lifted_map = MAM.getResult<LiftedFunctionAnalysis>(M);
  auto &DL = M.getDataLayout();

  StateFieldMap field_map(M);
  SafeOffsetMask safe_mask(field_map);

  llvm::DenseMap<llvm::Function *, PerFunctionInfo> info;

  // Phase A: compute TLI bottom-up. Iterate each SCC to fixpoint. For
  // singleton SCCs without self-edges this converges in one round (plus
  // one no-change round); for true cycles (mutual or self-recursion) we
  // iterate until the lattice stabilises.
  for (auto &scc : call_graph.getBottomUpSCCs()) {
    for (auto *F : scc) {
      if (!F || F->isDeclaration()) continue;
      info[F];  // default-construct empty
    }

    const unsigned scc_sz = static_cast<unsigned>(scc.size());
    const unsigned max_rounds = scc_sz <= 1 ? 4u : 16u * scc_sz;
    for (unsigned round = 0; round < max_rounds; ++round) {
      bool changed = false;
      for (auto *F : scc) {
        if (!F || F->isDeclaration()) continue;
        LiveSet new_tli =
            computeFunctionTLI(*F, DL, info, call_graph, lifted_map);
        auto &pfi = info[F];
        if (!pfi.tli.equals(new_tli)) {
          pfi.tli = std::move(new_tli);
          changed = true;
        }
      }
      if (!changed) break;
    }

    for (auto *F : scc) {
      if (!F || F->isDeclaration()) continue;
      info[F].tli_computed = true;
    }
  }

  // Phase B: rewrite each lifted function.
  unsigned total_erased = 0;
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    if (!isLiftedPipelineFunctionLocal(F)) continue;
    if (F.hasFnAttribute("omill.ipdse_done")) continue;

    // Only process functions with the canonical lifted signature.
    auto *FT = F.getFunctionType();
    if (FT->getNumParams() != 3) continue;
    if (!FT->getParamType(0)->isPointerTy()) continue;
    if (!FT->getParamType(2)->isPointerTy()) continue;

    total_erased +=
        rewriteFunction(F, DL, info, call_graph, lifted_map, safe_mask);
    F.addFnAttr("omill.ipdse_done");
  }

  if (std::getenv("OMILL_IPDSE_VERBOSE")) {
    unsigned all_count = 0;
    unsigned total = 0;
    for (auto &[F, pfi] : info) {
      if (!F || F->isDeclaration()) continue;
      ++total;
      if (pfi.tli.all) ++all_count;
    }
    llvm::errs() << "[ipdse] functions=" << total
                 << " TLI=all=" << all_count
                 << " erased=" << total_erased << "\n";
  }

  if (total_erased == 0) {
    return llvm::PreservedAnalyses::all();
  }
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
