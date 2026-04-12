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
#include <llvm/Transforms/Utils/Cloning.h>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
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
        if (!callee || !isDispatchCallName(callee->getName())) continue;
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
                       << constants.size() << "\n";
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
    if (!clone) continue;
    if (std::getenv("OMILL_DEBUG_STATE_IPCP"))
      llvm::errs() << "[ipcp] cloned " << site.target->getName()
                   << " -> " << clone->getName() << "\n";

    // Rewrite dispatch_call → direct call to clone.
    llvm::IRBuilder<> Builder(site.call);
    auto *nc = Builder.CreateCall(clone->getFunctionType(), clone,
        {site.call->getArgOperand(0), site.call->getArgOperand(1),
         site.call->getArgOperand(2)});
    nc->copyMetadata(*site.call);
    site.call->replaceAllUsesWith(nc);
    site.call->eraseFromParent();
    changed = true;
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
