#include "omill/Passes/InterProceduralConstProp.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/FormatVariadic.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Utils/Cloning.h>

#include <deque>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Passes/CombinedFixedPointDevirt.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

static constexpr const char *kWin64ParamRegs[] = {"RCX", "RDX", "R8", "R9"};

/// Resolve a pointer to its byte offset into the State struct (arg0).
int64_t resolveStateOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;
  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap)) {
        total_offset += ap.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base))
      { base = BC->getOperand(0); continue; }
    break;
  }
  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base))
    if (arg->getArgNo() == 0 && total_offset >= 0)
      return total_offset;
  return -1;
}

using StateConstants = llvm::DenseMap<unsigned, llvm::ConstantInt *>;

/// Collect constant stores to Win64 param offsets in the same BB before CI.
StateConstants collectPreCallConstants(
    llvm::CallInst *CI, const llvm::DataLayout &DL,
    const llvm::DenseSet<unsigned> &param_offsets) {
  StateConstants result;
  llvm::DenseSet<unsigned> seen;
  auto *BB = CI->getParent();
  auto it = CI->getIterator();
  while (it != BB->begin()) {
    --it;
    auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it);
    if (!SI) continue;
    int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
    if (off < 0) continue;
    unsigned u = static_cast<unsigned>(off);
    if (!param_offsets.count(u) || seen.count(u)) continue;
    seen.insert(u);
    if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand()))
      result[u] = C;
  }
  return result;
}

/// Scan a basic block backward collecting constant State stores.
static void collectStateConstantsInBlock(
    llvm::BasicBlock *BB, llvm::BasicBlock::iterator end_it,
    const llvm::DataLayout &DL,
    llvm::DenseSet<unsigned> &seen, StateConstants &result) {
  auto it = end_it;
  while (it != BB->begin()) {
    --it;
    auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it);
    if (!SI) continue;
    int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
    if (off < 0) continue;
    unsigned u = static_cast<unsigned>(off);
    if (seen.count(u)) continue;
    seen.insert(u);
    auto *val = SI->getValueOperand();
    if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(val)) {
      result[u] = C;
    } else if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(val)) {
      // Handle: store (add %program_counter, <const>)
      if (binop->getOpcode() == llvm::Instruction::Add) {
        llvm::ConstantInt *pc_offset = nullptr;
        llvm::Argument *pc_arg = nullptr;
        for (unsigned i = 0; i < 2; ++i) {
          if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(i)))
            pc_offset = ci;
          if (auto *a = llvm::dyn_cast<llvm::Argument>(binop->getOperand(i)))
            if (a->getArgNo() == 1) pc_arg = a;
        }
        if (pc_arg && pc_offset) {
          uint64_t va = extractEntryVA(BB->getParent()->getName());
          if (va == 0) va = extractBlockPC(BB->getParent()->getName());
          if (va != 0)
            result[u] = llvm::cast<llvm::ConstantInt>(
                llvm::ConstantInt::get(pc_offset->getType(),
                                        va + pc_offset->getZExtValue()));
        }
      }
    }
  }
}

/// Collect constant State stores at all function exits.
/// Intersects across exits: only keeps offsets where every exit agrees.
static StateConstants collectExitConstants(
    llvm::Function &F, const llvm::DataLayout &DL) {
  llvm::SmallVector<StateConstants, 4> per_exit;
  for (auto &BB : F) {
    if (!llvm::isa<llvm::ReturnInst>(BB.getTerminator())) continue;
    StateConstants consts;
    llvm::DenseSet<unsigned> seen;
    auto *cur = const_cast<llvm::BasicBlock *>(&BB);
    for (unsigned depth = 0; depth < 16; ++depth) {
      collectStateConstantsInBlock(cur, cur->end(), DL, seen, consts);
      auto *sp = cur->getSinglePredecessor();
      if (!sp || sp == cur || sp->getParent() != BB.getParent()) break;
      cur = sp;
    }
    per_exit.push_back(std::move(consts));
  }
  if (per_exit.empty()) return StateConstants();
  StateConstants result = per_exit[0];
  for (unsigned i = 1; i < per_exit.size(); ++i) {
    llvm::SmallVector<unsigned, 4> drop;
    for (auto &[off, c] : result) {
      auto it = per_exit[i].find(off);
      if (it == per_exit[i].end() ||
          it->second->getValue() != c->getValue())
        drop.push_back(off);
    }
    for (unsigned k : drop) result.erase(k);
  }
  return result;
}

/// Collect constant State stores in the local block before a call site.
/// Unlike the old collectAllPreCallStateConstants, this does NOT walk
/// backward through musttail callers — the worklist handles that.
static StateConstants collectLocalPreCallConstants(
    llvm::CallInst *CI, const llvm::DataLayout &DL) {
  StateConstants result;
  llvm::DenseSet<unsigned> seen;
  auto *BB = CI->getParent();
  collectStateConstantsInBlock(BB, CI->getIterator(), DL, seen, result);
  // Also walk single-predecessor chain within the same function.
  auto *pred = BB;
  for (unsigned pd = 0; pd < 16; ++pd) {
    auto *sp = pred->getSinglePredecessor();
    if (!sp || sp == pred || sp->getParent() != BB->getParent()) break;
    collectStateConstantsInBlock(sp, sp->end(), DL, seen, result);
    pred = sp;
  }
  return result;
}

/// Clone callee with constant State fields folded in.
/// Finds GEPs at the constant offsets (all blocks) and replaces their
/// load users with the constant.  Returns nullptr if no loads replaced.
static llvm::Function *cloneWithStateConstants(
    llvm::Module &M, llvm::Function &callee,
    const StateConstants &constants, const llvm::DataLayout &DL,
    llvm::StringRef suffix) {
  llvm::ValueToValueMapTy vmap;
  auto *clone = llvm::CloneFunction(&callee, vmap);
  clone->setName(callee.getName() + "__sc_" + suffix);
  clone->setLinkage(llvm::GlobalValue::InternalLinkage);
  clone->addFnAttr("omill.state_const_specialized");
  if (callee.hasFnAttribute("omill.block_lifter"))
    clone->addFnAttr("omill.block_lifter");

  auto *state_ptr = clone->getArg(0);
  bool any_replaced = false;

  for (auto &[offset, constant] : constants) {
    llvm::GetElementPtrInst *gep = nullptr;
    for (auto &BB : *clone) {
      for (auto &I : BB) {
        auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(&I);
        if (!G) continue;
        llvm::APInt ap(64, 0);
        if (!G->accumulateConstantOffset(DL, ap)) continue;
        if (ap.getSExtValue() != static_cast<int64_t>(offset)) continue;
        if (G->getPointerOperand() == state_ptr) { gep = G; break; }
      }
      if (gep) break;
    }
    if (!gep) continue;

    llvm::SmallVector<llvm::LoadInst *, 4> loads;
    for (auto *user : gep->users())
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(user))
        if (LI->getType() == constant->getType())
          loads.push_back(LI);
    for (auto *LI : loads) {
      LI->replaceAllUsesWith(constant);
      any_replaced = true;
    }
  }

  if (!any_replaced) { clone->eraseFromParent(); return nullptr; }
  return clone;
}

/// Compute which State offsets a function accesses.
static llvm::DenseSet<unsigned> getAccessedOffsets(
    llvm::Function &F, const llvm::DataLayout &DL) {
  llvm::DenseSet<unsigned> offsets;
  for (auto &BB : F)
    for (auto &I : BB) {
      if (auto *G = llvm::dyn_cast<llvm::GetElementPtrInst>(&I)) {
        llvm::APInt ap(64, 0);
        if (G->accumulateConstantOffset(DL, ap))
          offsets.insert(static_cast<unsigned>(ap.getSExtValue()));
      }
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) offsets.insert(static_cast<unsigned>(off));
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) offsets.insert(static_cast<unsigned>(off));
      }
    }
  return offsets;
}

/// For a given function, replace entry-block loads from State at a given
/// offset with a constant.  Used by the Win64 param IPCP path.
static bool replaceEntryBlockLoads(llvm::Function &F, unsigned offset,
                                   llvm::ConstantInt *C,
                                   const llvm::DataLayout &DL) {
  if (F.empty()) return false;
  bool changed = false;
  llvm::SmallVector<llvm::LoadInst *, 4> to_replace;
  for (auto &I : F.getEntryBlock()) {
    auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
    if (!LI) continue;
    int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
    if (off < 0 || static_cast<unsigned>(off) != offset) continue;
    if (LI->getType() != C->getType()) continue;
    to_replace.push_back(LI);
  }
  for (auto *LI : to_replace) {
    LI->replaceAllUsesWith(C);
    changed = true;
  }
  return changed;
}

/// Compute a hash for a set of State constants (for clone cache keying).
static uint64_t hashConstants(const StateConstants &consts) {
  uint64_t h = 0;
  for (auto &[off, c] : consts)
    h ^= llvm::hash_combine(off, c->getZExtValue());
  return h;
}

/// Look up a function by PC (sub_<hex> or blk_<hex>).
static llvm::Function *resolveTargetByPC(llvm::Module &M, uint64_t pc) {
  llvm::SmallString<32> buf;
  if (auto *F = M.getFunction(
          ("sub_" + llvm::Twine::utohexstr(pc)).toStringRef(buf)))
    return F;
  buf.clear();
  return M.getFunction(
      ("blk_" + llvm::Twine::utohexstr(pc)).toStringRef(buf));
}

/// Run the optimization pipeline on a freshly-cloned function.
static void optimizeClone(llvm::Function &clone, llvm::Module &M,
                          llvm::ModuleAnalysisManager &MAM) {
  auto &FAM =
      MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();
  llvm::FunctionPassManager FPM;
  FPM.addPass(CombinedFixedPointDevirtPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::GVNPass());
  auto PA = FPM.run(clone, FAM);
  FAM.invalidate(clone, PA);
}

// ===----------------------------------------------------------------------===
// State flow graph edge types
// ===----------------------------------------------------------------------===

enum class EdgeKind { kDispatchCall, kDispatchJump, kMusttail };

struct StateFlowEdge {
  EdgeKind kind;
  llvm::CallInst *site;
  llvm::Function *source;
  llvm::Function *target;   // resolved target (nullptr if unresolved)
  uint64_t target_pc = 0;   // for dispatch edges: the constant PC operand
};

/// Find all musttail call edges in a function.
static void findMusttailEdges(llvm::Function &F,
                              llvm::SmallVectorImpl<StateFlowEdge> &edges) {
  for (auto &BB : F) {
    auto *term = BB.getTerminator();
    if (!llvm::isa<llvm::ReturnInst>(term)) continue;
    auto *prev = term->getPrevNode();
    if (!prev) continue;
    auto *ci = llvm::dyn_cast<llvm::CallInst>(prev);
    if (!ci || (!ci->isMustTailCall() && !ci->isTailCall())) continue;
    auto *target = ci->getCalledFunction();
    if (!target) continue;
    edges.push_back({EdgeKind::kMusttail, ci, &F, target, 0});
  }
}

/// Find all dispatch_call and dispatch_jump edges in a function.
static void findDispatchEdges(llvm::Function &F, llvm::Module &M,
                              llvm::SmallVectorImpl<StateFlowEdge> &edges) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI || CI->arg_size() < 3) continue;
      auto *callee = CI->getCalledFunction();
      if (!callee) continue;
      bool is_call = isDispatchCallName(callee->getName());
      bool is_jump = isDispatchJumpName(callee->getName());
      if (!is_call && !is_jump) continue;
      auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
      if (!pc_arg) continue;
      uint64_t pc = pc_arg->getZExtValue();
      auto *target = resolveTargetByPC(M, pc);
      edges.push_back({is_call ? EdgeKind::kDispatchCall
                                : EdgeKind::kDispatchJump,
                       CI, &F, target, pc});
    }
  }
}

static bool debugEnabled() {
  static bool enabled = std::getenv("OMILL_DEBUG_STATE_IPCP") != nullptr;
  return enabled;
}

// ===----------------------------------------------------------------------===
// Worklist-based State constant propagation
// ===----------------------------------------------------------------------===

struct WorklistEntry {
  llvm::Function *target;
  StateConstants input;
  uint64_t hash;
  // The call site to rewrite (for dispatch edges).
  llvm::CallInst *dispatch_site = nullptr;
  EdgeKind edge_kind = EdgeKind::kMusttail;
  // The musttail call to rewrite (for musttail edges).
  llvm::CallInst *musttail_site = nullptr;
  // If true, this is an analysis-only entry: clone for constant extraction
  // but don't follow successor edges (prevents exponential cascading).
  bool analysis_only = false;
};

}  // namespace

bool propagateStateConstantsWorklist(
    llvm::Module &M, const llvm::DataLayout &DL,
    llvm::ModuleAnalysisManager *MAM,
    IPCPLiftCallback lift_callback) {
  bool changed = false;

  // Clone cache: (original function, input hash) → specialized clone.
  llvm::DenseMap<std::pair<llvm::Function *, uint64_t>, llvm::Function *>
      clone_cache;
  // Output cache: (original function, input hash) → output constants.
  llvm::DenseMap<std::pair<llvm::Function *, uint64_t>, StateConstants>
      output_cache;
  // Track which (function, hash) pairs have been fully processed.
  llvm::DenseSet<std::pair<llvm::Function *, uint64_t>> processed;

  std::deque<WorklistEntry> worklist;

  // Phase 1: Scan module for dispatch edges and seed the worklist.
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    llvm::SmallVector<StateFlowEdge, 4> edges;
    findDispatchEdges(F, M, edges);

    for (auto &edge : edges) {
      if (!edge.target || edge.target->isDeclaration()) continue;
      auto consts = collectLocalPreCallConstants(edge.site, DL);
      if (consts.empty()) continue;
      uint64_t h = hashConstants(consts);

      if (debugEnabled()) {
        llvm::errs() << "[ipcp] seed " << F.getName() << " -> "
                     << edge.target->getName()
                     << " kind=" << (edge.kind == EdgeKind::kDispatchCall
                                         ? "call" : "jump")
                     << " consts=" << consts.size();
        for (auto &[off, c] : consts)
          llvm::errs() << " [" << off << "]=0x"
                       << llvm::Twine::utohexstr(c->getZExtValue());
        llvm::errs() << "\n";
      }

      worklist.push_back({edge.target, std::move(consts), h,
                          edge.site, edge.kind, nullptr});
    }
  }

  if (debugEnabled())
    llvm::errs() << "[ipcp] worklist seeded: " << worklist.size()
                 << " entries\n";

  // Phase 2: Process worklist.
  unsigned iterations = 0;
  constexpr unsigned kMaxIterations = 128;

  while (!worklist.empty() && iterations < kMaxIterations) {
    ++iterations;
    auto entry = std::move(worklist.front());
    worklist.pop_front();

    auto key = std::make_pair(entry.target, entry.hash);

    // If the target is a declaration, try to lift it.
    if (entry.target->isDeclaration()) {
      uint64_t pc = extractBlockPC(entry.target->getName());
      if (pc == 0) pc = extractEntryVA(entry.target->getName());
      if (pc != 0 && lift_callback) {
        lift_callback(pc);
      }
      if (entry.target->isDeclaration()) continue;
    }

    // Skip if already processed with these exact constants.
    if (processed.count(key)) {
      // Still need to rewrite call sites using the cached clone.
      auto cache_it = clone_cache.find(key);
      llvm::Function *clone = (cache_it != clone_cache.end())
                                  ? cache_it->second : nullptr;
      if (clone) {
        if (entry.dispatch_site &&
            (entry.edge_kind == EdgeKind::kDispatchCall ||
             entry.edge_kind == EdgeKind::kDispatchJump)) {
          // Rewrite dispatch → direct call.
          llvm::IRBuilder<> Builder(entry.dispatch_site);
          auto *nc = Builder.CreateCall(
              clone->getFunctionType(), clone,
              {entry.dispatch_site->getArgOperand(0),
               entry.dispatch_site->getArgOperand(1),
               entry.dispatch_site->getArgOperand(2)});
          nc->copyMetadata(*entry.dispatch_site);
          entry.dispatch_site->replaceAllUsesWith(nc);
          entry.dispatch_site->eraseFromParent();
          changed = true;
        }
        if (entry.musttail_site) {
          entry.musttail_site->setCalledFunction(clone);
          changed = true;
        }
      }

      // Propagate cached output along successor edges.
      auto out_it = output_cache.find(key);
      if (out_it != output_cache.end() && !out_it->second.empty()) {
        // For dispatch_call: find musttail successors in the CALLER
        // and enqueue them with the output constants.
        if (entry.edge_kind == EdgeKind::kDispatchCall &&
            entry.dispatch_site) {
          // dispatch_site was erased above, use the replacement.
          // The caller function is the one that contained the dispatch.
          // We need to find it from the clone or the original.
        }
        // For musttail and dispatch_jump: find successors of the target.
        // Don't pass call sites from inside clones — only propagate
        // constants, don't rewrite inner IR.
        llvm::Function *effective = clone ? clone : entry.target;
        llvm::SmallVector<StateFlowEdge, 4> succ_edges;
        findMusttailEdges(*effective, succ_edges);
        findDispatchEdges(*effective, M, succ_edges);
        for (auto &se : succ_edges) {
          if (!se.target) continue;
          uint64_t sh = hashConstants(out_it->second);
          auto sk = std::make_pair(se.target, sh);
          if (processed.count(sk)) continue;
          worklist.push_back({se.target, out_it->second, sh,
                              nullptr, se.kind, nullptr});
        }
      }
      continue;
    }

    // Clone + specialize.
    auto cache_it = clone_cache.find(key);
    llvm::Function *clone = nullptr;
    bool from_cache = (cache_it != clone_cache.end());
    if (from_cache) {
      clone = cache_it->second;
    } else {
      llvm::SmallString<16> sfx;
      llvm::raw_svector_ostream(sfx)
          << llvm::format_hex_no_prefix(entry.hash, 8);
      clone = cloneWithStateConstants(M, *entry.target, entry.input, DL, sfx);
      clone_cache[key] = clone;
    }

    // Optimize the clone.
    if (clone && !from_cache && MAM) {
      optimizeClone(*clone, M, *MAM);
      if (debugEnabled())
        llvm::errs() << "[ipcp] optimized clone " << clone->getName() << "\n";
    }

    // Extract output constants.
    StateConstants output;
    if (clone) {
      output = collectExitConstants(*clone, DL);
    }
    // Pass-through: input constants for offsets the target doesn't access.
    auto accessed = getAccessedOffsets(clone ? *clone : *entry.target, DL);
    for (auto &[off, c] : entry.input) {
      if (!accessed.count(off) && !output.count(off))
        output[off] = c;
    }

    output_cache[key] = output;
    processed.insert(key);

    if (debugEnabled()) {
      llvm::errs() << "[ipcp] processed " << entry.target->getName()
                   << " hash=" << llvm::format_hex(entry.hash, 10)
                   << " clone=" << (clone ? clone->getName() : "<none>")
                   << " output=" << output.size() << "\n";
      if (!output.empty()) {
        llvm::errs() << "[ipcp]   output:";
        for (auto &[off, c] : output)
          llvm::errs() << " [" << off << "]=0x"
                       << llvm::Twine::utohexstr(c->getZExtValue());
        llvm::errs() << "\n";
      }
    }

    // Rewrite the call site.
    if (clone) {
      if (entry.dispatch_site &&
          (entry.edge_kind == EdgeKind::kDispatchCall ||
           entry.edge_kind == EdgeKind::kDispatchJump)) {
        llvm::IRBuilder<> Builder(entry.dispatch_site);
        auto *nc = Builder.CreateCall(
            clone->getFunctionType(), clone,
            {entry.dispatch_site->getArgOperand(0),
             entry.dispatch_site->getArgOperand(1),
             entry.dispatch_site->getArgOperand(2)});
        nc->copyMetadata(*entry.dispatch_site);
        entry.dispatch_site->replaceAllUsesWith(nc);
        entry.dispatch_site->eraseFromParent();
        entry.dispatch_site = nullptr;
        changed = true;
      }
      if (entry.musttail_site) {
        entry.musttail_site->setCalledFunction(clone);
        changed = true;
      }
    }

    // Propagate output along successor edges.
    if (output.empty()) continue;

    // For dispatch_call: the callee returns, then the CALLER's musttail
    // successors see the merged constants (input + callee output).
    // For dispatch_call, also look for dispatch edges INSIDE the clone
    // to follow nested dispatch_call chains (e.g. VMP init).
    llvm::Function *effective = clone ? clone : entry.target;

    // Find dispatch edges inside the clone/target (recursive discovery).
    // These are enqueued as analysis_only: cloned for constant extraction
    // but successors are NOT followed (prevents exponential cascading).
    if (!entry.analysis_only) {
      llvm::SmallVector<StateFlowEdge, 4> inner_edges;
      findDispatchEdges(*effective, M, inner_edges);
      for (auto &ie : inner_edges) {
        if (!ie.target) {
          ie.target = resolveTargetByPC(M, ie.target_pc);
          if (!ie.target && lift_callback) {
            lift_callback(ie.target_pc);
            ie.target = resolveTargetByPC(M, ie.target_pc);
          }
        }
        if (!ie.target) continue;
        uint64_t sh = hashConstants(output);
        auto sk = std::make_pair(ie.target, sh);
        if (!processed.count(sk)) {
          if (debugEnabled())
            llvm::errs() << "[ipcp] inner dispatch "
                         << effective->getName() << " -> "
                         << ie.target->getName()
                         << " kind="
                         << (ie.kind == EdgeKind::kDispatchCall
                                 ? "call" : "jump")
                         << "\n";
          worklist.push_back({ie.target, output, sh,
                              nullptr, ie.kind, nullptr,
                              /*analysis_only=*/true});
        }
      }
    }

    // NOTE: We do NOT follow musttail edges from the TARGET here.
    // The target's musttail chain belongs to a shared function — rewriting
    // musttail calls there would break other callers. Instead, Phase 3
    // handles the CALLER's musttail chain (after the dispatch_call returns,
    // the caller musttails to successor blocks that see merged constants).

    // For dispatch_call edges: also propagate to the CALLER's musttail
    // successors. After the dispatch_call returns, the caller musttails
    // to successor blocks that should see the merged constants.
    if (entry.edge_kind == EdgeKind::kDispatchCall && entry.dispatch_site) {
      // dispatch_site was erased above if clone succeeded.
      // Use the original caller function to find musttail successors.
      // The caller is entry.dispatch_site's parent — but it was erased.
      // We need to handle this differently: the caller function is the
      // source of the dispatch edge, tracked separately.
    }
  }

  // Phase 3: Second pass — propagate from dispatch_call callers.
  // After processing all dispatch_call targets, propagate output constants
  // from callee clones to the caller's musttail successors.
  // We do this as a separate pass because the dispatch_call site gets
  // erased during rewriting, so we need to track caller→callee mappings.
  {
    // Re-scan the module for callers that invoke our clones.
    // For each clone call site, find the caller's musttail successors
    // and merge the callee's output constants into the successor's input.
    for (auto &F : M) {
      if (F.isDeclaration()) continue;
      // Find dispatch_call sites that were rewritten to clone calls.
      for (auto &BB : F) {
        for (auto &I : BB) {
          auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
          if (!CI) continue;
          auto *callee = CI->getCalledFunction();
          if (!callee || !callee->hasFnAttribute("omill.state_const_specialized"))
            continue;
          // This is a rewritten dispatch_call → clone call.
          // Collect the pre-call constants in the caller.
          auto caller_consts = collectLocalPreCallConstants(CI, DL);

          // Find the clone's output in the cache.
          // We need to match by clone pointer.
          StateConstants callee_output;
          for (auto &[k, v] : output_cache) {
            auto clone_it = clone_cache.find(k);
            if (clone_it != clone_cache.end() &&
                clone_it->second == callee) {
              callee_output = v;
              break;
            }
          }

          // Merge: caller pre-call + callee output (callee wins).
          StateConstants merged = caller_consts;
          for (auto &[off, c] : callee_output)
            merged[off] = c;

          if (merged.empty()) continue;
          uint64_t mh = hashConstants(merged);

          // Find musttail successors of the caller.
          llvm::SmallVector<StateFlowEdge, 4> caller_mt;
          findMusttailEdges(F, caller_mt);
          for (auto &me : caller_mt) {
            if (!me.target) continue;
            if (me.target->isDeclaration()) {
              uint64_t pc = extractBlockPC(me.target->getName());
              if (pc == 0) pc = extractEntryVA(me.target->getName());
              if (pc != 0 && lift_callback)
                lift_callback(pc);
              if (me.target->isDeclaration()) continue;
            }
            auto sk = std::make_pair(me.target, mh);
            if (processed.count(sk)) {
              // Still rewrite the musttail site.
              auto cit = clone_cache.find(sk);
              if (cit != clone_cache.end() && cit->second) {
                me.site->setCalledFunction(cit->second);
                changed = true;
              }
              continue;
            }
            if (debugEnabled())
              llvm::errs() << "[ipcp] caller-mt " << F.getName()
                           << " -> " << me.target->getName()
                           << " merged=" << merged.size() << "\n";
            worklist.push_back({me.target, merged, mh,
                                nullptr, EdgeKind::kMusttail, me.site});
          }
        }
      }
    }

    // Process the caller-mt entries.
    while (!worklist.empty() && iterations < kMaxIterations) {
      ++iterations;
      auto entry = std::move(worklist.front());
      worklist.pop_front();
      auto key = std::make_pair(entry.target, entry.hash);

      if (entry.target->isDeclaration()) {
        uint64_t pc = extractBlockPC(entry.target->getName());
        if (pc == 0) pc = extractEntryVA(entry.target->getName());
        if (pc != 0 && lift_callback) lift_callback(pc);
        if (entry.target->isDeclaration()) continue;
      }

      if (processed.count(key)) {
        auto cit = clone_cache.find(key);
        if (cit != clone_cache.end() && cit->second && entry.musttail_site) {
          entry.musttail_site->setCalledFunction(cit->second);
          changed = true;
        }
        // Continue propagating to successors.
        auto out_it = output_cache.find(key);
        if (out_it != output_cache.end() && !out_it->second.empty()) {
          llvm::Function *eff = (cit != clone_cache.end() && cit->second)
                                    ? cit->second : entry.target;
          llvm::SmallVector<StateFlowEdge, 4> succ;
          findMusttailEdges(*eff, succ);
          findDispatchEdges(*eff, M, succ);
          for (auto &se : succ) {
            if (!se.target) continue;
            if (se.target->isDeclaration()) {
              uint64_t pc = extractBlockPC(se.target->getName());
              if (pc == 0) pc = extractEntryVA(se.target->getName());
              if (pc != 0 && lift_callback) lift_callback(pc);
              if (se.target->isDeclaration()) continue;
            }
            uint64_t sh = hashConstants(out_it->second);
            auto sk = std::make_pair(se.target, sh);
            if (!processed.count(sk))
              worklist.push_back({se.target, out_it->second, sh,
                                  nullptr, se.kind, nullptr});
          }
        }
        continue;
      }

      // Clone + specialize + optimize.
      auto cache_it = clone_cache.find(key);
      llvm::Function *clone = nullptr;
      bool from_cache = (cache_it != clone_cache.end());
      if (from_cache) {
        clone = cache_it->second;
      } else {
        llvm::SmallString<16> sfx;
        llvm::raw_svector_ostream(sfx)
            << llvm::format_hex_no_prefix(entry.hash, 8);
        clone = cloneWithStateConstants(
            M, *entry.target, entry.input, DL, sfx);
        clone_cache[key] = clone;
      }
      if (clone && !from_cache && MAM) {
        optimizeClone(*clone, M, *MAM);
        if (debugEnabled())
          llvm::errs() << "[ipcp] optimized " << clone->getName() << "\n";
      }

      StateConstants output;
      if (clone) output = collectExitConstants(*clone, DL);
      auto accessed = getAccessedOffsets(clone ? *clone : *entry.target, DL);
      for (auto &[off, c] : entry.input)
        if (!accessed.count(off) && !output.count(off))
          output[off] = c;

      output_cache[key] = output;
      processed.insert(key);

      if (debugEnabled())
        llvm::errs() << "[ipcp] processed " << entry.target->getName()
                     << " clone=" << (clone ? clone->getName() : "<none>")
                     << " output=" << output.size() << "\n";

      if (clone) {
        if (entry.musttail_site) {
          entry.musttail_site->setCalledFunction(clone);
          changed = true;
        }
        if (entry.dispatch_site) {
          llvm::IRBuilder<> Builder(entry.dispatch_site);
          auto *nc = Builder.CreateCall(
              clone->getFunctionType(), clone,
              {entry.dispatch_site->getArgOperand(0),
               entry.dispatch_site->getArgOperand(1),
               entry.dispatch_site->getArgOperand(2)});
          nc->copyMetadata(*entry.dispatch_site);
          entry.dispatch_site->replaceAllUsesWith(nc);
          entry.dispatch_site->eraseFromParent();
          changed = true;
        }
      }

      if (output.empty()) continue;
      llvm::Function *eff = clone ? clone : entry.target;
      llvm::SmallVector<StateFlowEdge, 4> succ;
      findMusttailEdges(*eff, succ);
      findDispatchEdges(*eff, M, succ);
      for (auto &se : succ) {
        if (!se.target) {
          if (se.kind != EdgeKind::kMusttail)
            se.target = resolveTargetByPC(M, se.target_pc);
          if (!se.target) continue;
        }
        if (se.target->isDeclaration()) {
          uint64_t pc = extractBlockPC(se.target->getName());
          if (pc == 0) pc = extractEntryVA(se.target->getName());
          if (pc != 0 && lift_callback) lift_callback(pc);
          if (se.target->isDeclaration()) continue;
        }
        uint64_t sh = hashConstants(output);
        auto sk = std::make_pair(se.target, sh);
        if (!processed.count(sk))
          worklist.push_back({se.target, output, sh,
                              nullptr, se.kind, nullptr});
      }
    }
  }

  // Phase 4: Clean up analysis-only clones.
  // Clones created for inner dispatch edges (constant extraction only) have
  // no callers. If left in the module, they pollute the function list and
  // cause the main pipeline (ITR) to hang trying to resolve their dispatch
  // calls. Delete any clone with no users.
  {
    llvm::SmallVector<llvm::Function *, 16> to_delete;
    for (auto &[key, clone] : clone_cache) {
      if (!clone) continue;
      if (clone->use_empty())
        to_delete.push_back(clone);
    }
    for (auto *F : to_delete) {
      if (debugEnabled())
        llvm::errs() << "[ipcp] deleting analysis-only clone "
                     << F->getName() << "\n";
      F->eraseFromParent();
    }
  }

  if (debugEnabled())
    llvm::errs() << "[ipcp] done: iterations=" << iterations
                 << " changed=" << changed << "\n";

  return changed;
}

// ===----------------------------------------------------------------------===
// Win64 param IPCP (original pass, unchanged)
// ===----------------------------------------------------------------------===

llvm::PreservedAnalyses InterProceduralConstPropPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &call_graph = MAM.getResult<CallGraphAnalysis>(M);
  auto &DL = M.getDataLayout();

  StateFieldMap field_map(M);
  llvm::DenseSet<unsigned> param_offsets;
  for (auto *reg_name : kWin64ParamRegs)
    if (auto field = field_map.fieldByName(reg_name))
      param_offsets.insert(field->offset);
  if (param_offsets.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;
  for (auto &scc : call_graph.getBottomUpSCCs()) {
    if (scc.size() != 1) continue;
    auto *F = scc[0];
    auto *node = call_graph.getNode(F);
    if (!node || node->callers.empty() || F->hasAddressTaken()) continue;

    for (unsigned offset : param_offsets) {
      llvm::ConstantInt *unanimous = nullptr;
      bool all_agree = true;
      for (auto *caller_cs : node->callers) {
        auto pre_call = collectPreCallConstants(caller_cs->inst, DL, param_offsets);
        auto it = pre_call.find(offset);
        if (it == pre_call.end()) { all_agree = false; break; }
        if (!unanimous) unanimous = it->second;
        else if (unanimous->getValue() != it->second->getValue())
          { all_agree = false; break; }
      }
      if (all_agree && unanimous)
        changed |= replaceEntryBlockLoads(*F, offset, unanimous, DL);
    }
  }
  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
