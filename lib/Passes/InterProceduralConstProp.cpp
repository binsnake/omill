#include "omill/Passes/InterProceduralConstProp.h"

#include <llvm/ADT/DenseMap.h>
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

using PreCallConstants = llvm::DenseMap<unsigned, llvm::ConstantInt *>;

/// Collect constant stores to Win64 param offsets in the same BB before CI.
PreCallConstants collectPreCallConstants(
    llvm::CallInst *CI, const llvm::DataLayout &DL,
    const llvm::DenseSet<unsigned> &param_offsets) {
  PreCallConstants result;
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
    llvm::DenseSet<unsigned> &seen, PreCallConstants &result) {
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

/// Collect constant State stores at all function exits, walking backward
/// through the exit block and its single-predecessor chain.
/// Intersects across exits: only keeps offsets where every exit agrees.
static PreCallConstants collectCalleeOutputConstants(
    llvm::Function &F, const llvm::DataLayout &DL) {
  llvm::SmallVector<PreCallConstants, 4> per_exit;
  for (auto &BB : F) {
    if (!llvm::isa<llvm::ReturnInst>(BB.getTerminator())) continue;
    PreCallConstants consts;
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
  if (per_exit.empty()) return PreCallConstants();
  // Intersect: only offsets where all exits agree on the same value.
  PreCallConstants result = per_exit[0];
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

/// Collect ALL constant stores before a dispatch_call, walking backward
/// through musttail caller chains and single-predecessor blocks.
PreCallConstants collectAllPreCallStateConstants(
    llvm::CallInst *CI, const llvm::DataLayout &DL) {
  PreCallConstants result;
  llvm::DenseSet<unsigned> seen;
  auto *BB = CI->getParent();
  collectStateConstantsInBlock(BB, CI->getIterator(), DL, seen, result);

  // Walk up musttail caller chain.
  auto *F = BB->getParent();
  for (unsigned depth = 0; depth < 8; ++depth) {
    llvm::CallInst *caller_ci = nullptr;
    unsigned count = 0;
    for (auto *user : F->users()) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(user);
      if (call && (call->isMustTailCall() || call->isTailCall()))
        { caller_ci = call; ++count; }
    }
    if (count != 1 || !caller_ci) break;
    auto *caller_bb = caller_ci->getParent();
    collectStateConstantsInBlock(caller_bb, caller_ci->getIterator(),
                                 DL, seen, result);
    // Follow single-predecessor chain in caller function.
    auto *pred = caller_bb;
    for (unsigned pd = 0; pd < 16; ++pd) {
      auto *sp = pred->getSinglePredecessor();
      if (!sp || sp == pred || sp->getParent() != caller_bb->getParent()) break;
      collectStateConstantsInBlock(sp, sp->end(), DL, seen, result);
      pred = sp;
    }
    F = caller_bb->getParent();
  }
  return result;
}

/// Clone callee with constant State fields folded in.
/// Finds GEPs at the constant offsets (all blocks) and replaces their
/// load users with the constant.  Returns nullptr if no loads replaced.
llvm::Function *cloneWithStateConstants(
    llvm::Module &M, llvm::Function &callee,
    const PreCallConstants &constants, const llvm::DataLayout &DL,
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
    // Find GEP at this offset (any block).
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

    // Replace all loads through this GEP.
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
bool replaceEntryBlockLoads(llvm::Function &F, unsigned offset,
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

}  // namespace

// ===----------------------------------------------------------------------===
// Dispatch-call State constant propagation
// ===----------------------------------------------------------------------===

bool propagateStateConstantsThroughDispatches(
    llvm::Module &M, const llvm::DataLayout &DL,
    llvm::ModuleAnalysisManager *MAM,
    DerivedStateConstants *persistent_derived) {
  bool changed = false;
  llvm::DenseMap<std::pair<llvm::Function *, uint64_t>, llvm::Function *>
      clone_cache;

  struct DispatchSite {
    llvm::CallInst *call;
    llvm::Function *target;
    PreCallConstants constants;
  };
  llvm::SmallVector<DispatchSite, 8> sites;

  // Collect dispatch_call sites.
  for (auto &F : M) {
    if (F.isDeclaration()) continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI || CI->arg_size() < 3) continue;
        auto *callee = CI->getCalledFunction();
        if (!callee || (!isDispatchCallName(callee->getName()) &&
                       !isDispatchJumpName(callee->getName())))
          continue;
        auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1));
        if (!pc_arg) continue;
        uint64_t pc = pc_arg->getZExtValue();
        llvm::SmallString<32> buf;
        auto *target = M.getFunction(
            ("sub_" + llvm::Twine::utohexstr(pc)).toStringRef(buf));
        if (!target) {
          buf.clear();
          target = M.getFunction(
              ("blk_" + llvm::Twine::utohexstr(pc)).toStringRef(buf));
        }
        if (!target || target->isDeclaration()) continue;
        auto constants = collectAllPreCallStateConstants(CI, DL);
        if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
          llvm::errs() << "[ipcp] site " << F.getName() << " -> "
                       << target->getName() << " consts="
                       << constants.size();
        for (auto &[off, c] : constants)
          llvm::errs() << " [" << off << "]=0x"
                       << llvm::Twine::utohexstr(c->getZExtValue());
        llvm::errs() << "\n";
        sites.push_back({CI, target, std::move(constants)});
      }
    }
  }

  // Derived constants map (persistent across rounds if provided).
  DerivedStateConstants local;
  DerivedStateConstants &derived = persistent_derived ? *persistent_derived : local;

  if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
    llvm::errs() << "[ipcp] ENTER: derived.size()=" << derived.size() << "\n";

  // Pre-pass: compute pass-through for all sites.
  for (auto &site : sites) {
    auto accessed = getAccessedOffsets(*site.target, DL);
    for (auto &[off, c] : site.constants)
      if (!accessed.count(off) && !derived.count(off)) {
        derived[off] = c;
        if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
          llvm::errs() << "[ipcp] pre-pass: [" << off << "] pass-through "
                       << site.target->getName() << "\n";
      }
  }
  if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
    llvm::errs() << "[ipcp] pre-pass done: derived=" << derived.size()
                 << " sites=" << sites.size()
                 << " persistent=" << (persistent_derived != nullptr) << "\n";

  // Process each site.
  for (auto &site : sites) {
    // Re-collect (picks up constants from prior rewrites in same round).
    site.constants = collectAllPreCallStateConstants(site.call, DL);
    // Merge derived pass-through constants.
    for (auto &[off, c] : derived)
      if (!site.constants.count(off))
        site.constants[off] = c;
    if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
      llvm::errs() << "[ipcp] " << site.target->getName()
                   << " after merge: " << site.constants.size()
                   << " (derived=" << derived.size() << ")\n";
    if (site.constants.empty()) continue;

    // Per-constant pass-through: remove constants the target doesn't access.
    auto accessed = getAccessedOffsets(*site.target, DL);
    llvm::SmallVector<unsigned, 4> passthru;
    for (auto &[off, c] : site.constants)
      if (!accessed.count(off)) {
        derived[off] = c;
        passthru.push_back(off);
      }
    for (unsigned k : passthru) site.constants.erase(k);

    // If all constants passed through, follow musttail targets.
    // The constant flows through this function's musttail chain
    // to the next function that might access it.
    if (site.constants.empty() && !passthru.empty()) {
      for (auto &BB : *site.target) {
        auto *term = BB.getTerminator();
        if (!llvm::isa<llvm::ReturnInst>(term)) continue;
        auto *prev = term->getPrevNode();
        if (!prev) continue;
        auto *mci = llvm::dyn_cast<llvm::CallInst>(prev);
        if (!mci || (!mci->isMustTailCall() && !mci->isTailCall()))
          continue;
        auto *mt_fn = mci->getCalledFunction();
        if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
          llvm::errs() << "[ipcp] musttail target: "
                       << (mt_fn ? mt_fn->getName() : "<null>")
                       << " decl=" << (mt_fn && mt_fn->isDeclaration())
                       << "\n";
        if (!mt_fn || mt_fn->isDeclaration()) continue;
        auto mt_accessed = getAccessedOffsets(*mt_fn, DL);
        PreCallConstants mt_consts;
        for (unsigned k : passthru)
          if (mt_accessed.count(k))
            mt_consts[k] = derived[k];
        if (!mt_consts.empty()) {
          // Process this musttail target as a new site inline.
          uint64_t mt_hash = 0;
          for (auto &[o, cv] : mt_consts)
            mt_hash ^= llvm::hash_combine(o, cv->getZExtValue());
          auto mt_key = std::make_pair(mt_fn, mt_hash);
          if (!clone_cache.count(mt_key)) {
            llvm::SmallString<16> sfx;
            llvm::raw_svector_ostream(sfx)
                << llvm::format_hex_no_prefix(mt_hash, 8);
            auto *mt_clone = cloneWithStateConstants(
                M, *mt_fn, mt_consts, DL, sfx);
            clone_cache[mt_key] = mt_clone;
            if (mt_clone) {
              mci->setCalledFunction(mt_clone);
              changed = true;
              if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
                llvm::errs() << "[ipcp] cloned musttail "
                             << mt_fn->getName() << " -> "
                             << mt_clone->getName() << "\n";
            }
          }
        }
      }
      continue;
    }
    if (site.constants.empty()) continue;

    // Clone + specialize.
    uint64_t hash = 0;
    for (auto &[off, c] : site.constants)
      hash ^= llvm::hash_combine(off, c->getZExtValue());
    auto key = std::make_pair(site.target, hash);

    llvm::Function *clone = nullptr;
    auto cached = clone_cache.find(key);
    if (cached != clone_cache.end()) {
      clone = cached->second;
    } else {
      llvm::SmallString<16> sfx;
      llvm::raw_svector_ostream(sfx) << llvm::format_hex_no_prefix(hash, 8);
      clone = cloneWithStateConstants(M, *site.target, site.constants, DL, sfx);
      clone_cache[key] = clone;
    }
    // Step 3.5: Optimize clone and extract post-call State constants.
    if (clone) {
      bool from_cache = (cached != clone_cache.end());
      if (!from_cache && MAM) {
        auto &FAM =
            MAM->getResult<llvm::FunctionAnalysisManagerModuleProxy>(M)
                .getManager();
        llvm::FunctionPassManager FPM;
        FPM.addPass(CombinedFixedPointDevirtPass());
        FPM.addPass(llvm::InstCombinePass());
        FPM.addPass(llvm::GVNPass());
        auto PA = FPM.run(*clone, FAM);
        FAM.invalidate(*clone, PA);
        if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
          llvm::errs() << "[ipcp] optimized clone " << clone->getName() << "\n";
      }
      auto post_call = collectCalleeOutputConstants(*clone, DL);
      if (!post_call.empty()) {
        for (auto &[off, c] : post_call)
          site.constants[off] = c;
        hash = 0;
        for (auto &[off, c] : site.constants)
          hash ^= llvm::hash_combine(off, c->getZExtValue());
        if (std::getenv("OMILL_DEBUG_STATE_IPCP")) {
          llvm::errs() << "[ipcp] post-call constants for "
                       << site.target->getName() << ":";
          for (auto &[off, c] : post_call)
            llvm::errs() << " [" << off << "]=0x"
                         << llvm::Twine::utohexstr(c->getZExtValue());
          llvm::errs() << "\n";
        }
      }
      if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
        llvm::errs() << "[ipcp] cloned " << site.target->getName()
                     << " -> " << clone->getName() << "\n";
    }
    // Even when the clone fails (target doesn't use the constants),
    // still propagate through the musttail chain — the musttail
    // successors might use them (e.g. blk_1800018a6 uses R14).
    if (!clone && site.constants.empty()) continue;

    // Rewrite dispatch_call → direct call to clone (if clone succeeded).
    llvm::CallInst *nc = site.call;  // fallback: keep original
    if (clone) {
      llvm::IRBuilder<> Builder(site.call);
      nc = Builder.CreateCall(clone->getFunctionType(), clone,
          {site.call->getArgOperand(0), site.call->getArgOperand(1),
           site.call->getArgOperand(2)});
      nc->copyMetadata(*site.call);
      site.call->replaceAllUsesWith(nc);
      site.call->eraseFromParent();
      changed = true;
    }

    // Propagate constants through musttail successors of the clone.
    // When the clone musttails to blk_<pc>, that block inherits the
    // Propagate constants through the musttail chain from the
    // CALLER function.  The caller stores constants to State, then
    // after the dispatch_call returns, musttails to successor blocks.
    // Those successors load from State but can't see through the
    // function boundary — clone them with the constants baked in.
    {
      // Start from the caller function that contains the dispatch site.
      llvm::Function *chain_fn = nc->getParent()->getParent();
      if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
        llvm::errs() << "[ipcp] musttail-chain from "
                     << chain_fn->getName() << "\n";
      for (unsigned depth = 0; depth < 8; ++depth) {
        llvm::CallInst *mt_call = nullptr;
        for (auto &BB : *chain_fn) {
          auto *term = BB.getTerminator();
          if (!llvm::isa<llvm::ReturnInst>(term)) continue;
          if (auto *prev = term->getPrevNode())
            if (auto *ci = llvm::dyn_cast<llvm::CallInst>(prev))
              if (ci->isMustTailCall() || ci->isTailCall())
                mt_call = ci;
        }
        if (!mt_call) break;
        auto *mt_target = mt_call->getCalledFunction();
        if (!mt_target || mt_target->isDeclaration()) break;
        if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
          llvm::errs() << "[ipcp] mt-chain depth=" << depth
                       << " target=" << mt_target->getName() << "\n";

        auto mt_key = std::make_pair(mt_target, hash);
        if (clone_cache.count(mt_key)) break;

        llvm::SmallString<16> mt_sfx;
        llvm::raw_svector_ostream(mt_sfx)
            << llvm::format_hex_no_prefix(hash, 8);
        auto *mt_clone = cloneWithStateConstants(
            M, *mt_target, site.constants, DL, mt_sfx);
        if (mt_clone) {
          clone_cache[mt_key] = mt_clone;
          mt_call->setCalledFunction(mt_clone);
          changed = true;
          if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
            llvm::errs() << "[ipcp] mt-cloned "
                         << mt_target->getName() << " -> "
                         << mt_clone->getName() << "\n";
          chain_fn = mt_clone;
        } else {
          // Target doesn't use these constants — skip but continue
          // the chain from the ORIGINAL target (it might musttail
          // to a function that DOES use them).
          chain_fn = mt_target;
        }
      }
    }
  }

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
