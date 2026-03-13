#include "omill/Passes/ControlFlowUnflattener.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

namespace omill {

namespace {

void canonicalizePhiIncomingEdges(llvm::Function &F) {
  for (auto &BB : F) {
    llvm::DenseMap<llvm::BasicBlock *, unsigned> pred_edge_count;
    for (auto *pred : llvm::predecessors(&BB))
      ++pred_edge_count[pred];

    for (auto &I : llvm::make_early_inc_range(BB)) {
      auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
      if (!phi)
        break;

      for (unsigned i = phi->getNumIncomingValues(); i-- > 0;) {
        if (!pred_edge_count.count(phi->getIncomingBlock(i))) {
          phi->removeIncomingValue(i, /*DeletePHIIfEmpty=*/false);
        }
      }

      llvm::DenseMap<llvm::BasicBlock *, unsigned> phi_count;
      for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i)
        ++phi_count[phi->getIncomingBlock(i)];

      for (auto &[pred, needed] : pred_edge_count) {
        unsigned have = phi_count.lookup(pred);
        if (have == 0)
          continue;
        while (have > needed) {
          int idx = phi->getBasicBlockIndex(pred);
          if (idx < 0)
            break;
          phi->removeIncomingValue(static_cast<unsigned>(idx),
                                   /*DeletePHIIfEmpty=*/false);
          --have;
        }
        for (unsigned j = have; j < needed; ++j)
          phi->addIncoming(phi->getIncomingValueForBlock(pred), pred);
      }

      if (phi->getNumIncomingValues() == 0) {
        phi->replaceAllUsesWith(llvm::PoisonValue::get(phi->getType()));
        phi->eraseFromParent();
      }
    }
  }
}

/// Describes a switch-based dispatcher block used in CFF.
struct DispatcherInfo {
  llvm::BasicBlock *block;
  llvm::SwitchInst *sw;
  llvm::PHINode *state_phi;
  llvm::SmallVector<llvm::PHINode *, 8> all_phis;
  llvm::DenseMap<int64_t, llvm::BasicBlock *> state_to_block;
};

/// A resolved redirect: replace a back-edge with a direct branch.
struct Redirect {
  llvm::BasicBlock *src;
  llvm::BasicBlock *true_target;
  llvm::Value *condition = nullptr;      // null → unconditional
  llvm::BasicBlock *false_target = nullptr;
};

/// Detect whether a basic block is a CFF dispatcher.
///
/// Requirements:
///   - Terminates with a switch instruction
///   - Switch condition is a PHI node in the same block
///   - At least 3 switch cases
///   - More than half of the PHI's incoming blocks are switch successors
std::optional<DispatcherInfo> identifyDispatcher(llvm::BasicBlock *BB) {
  auto *sw = llvm::dyn_cast<llvm::SwitchInst>(BB->getTerminator());
  if (!sw || sw->getNumCases() < 3)
    return std::nullopt;

  auto *phi = llvm::dyn_cast<llvm::PHINode>(sw->getCondition());
  if (!phi || phi->getParent() != BB)
    return std::nullopt;

  // Collect switch successor set.
  llvm::DenseSet<llvm::BasicBlock *> succ_set;
  for (auto &c : sw->cases())
    succ_set.insert(c.getCaseSuccessor());

  // Count back-edges: PHI incoming from switch successors.
  unsigned back_edges = 0;
  for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
    if (succ_set.count(phi->getIncomingBlock(i)))
      ++back_edges;
  }

  // Require more than half of incoming values to be back-edges.
  if (back_edges * 2 <= phi->getNumIncomingValues())
    return std::nullopt;

  DispatcherInfo info;
  info.block = BB;
  info.sw = sw;
  info.state_phi = phi;

  for (auto &inst : *BB) {
    if (auto *p = llvm::dyn_cast<llvm::PHINode>(&inst))
      info.all_phis.push_back(p);
    else
      break;
  }

  for (auto &c : sw->cases())
    info.state_to_block[c.getCaseValue()->getSExtValue()] =
        c.getCaseSuccessor();

  return info;
}

/// Analyze a switch successor to see if it branches back to the dispatcher
/// with a resolvable next-state value.
std::optional<Redirect> analyzeBackEdge(llvm::BasicBlock *src,
                                        const DispatcherInfo &info) {
  // Require unconditional branch back to the dispatcher.
  auto *br = llvm::dyn_cast<llvm::BranchInst>(src->getTerminator());
  if (!br || br->isConditional() || br->getSuccessor(0) != info.block)
    return std::nullopt;

  llvm::Value *next_state = info.state_phi->getIncomingValueForBlock(src);
  if (!next_state)
    return std::nullopt;

  // Case 1: Constant next-state → unconditional redirect.
  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(next_state)) {
    auto it = info.state_to_block.find(ci->getSExtValue());
    if (it == info.state_to_block.end())
      return std::nullopt;
    if (it->second == src)
      return std::nullopt;  // Skip self-loops.
    return Redirect{src, it->second, nullptr, nullptr};
  }

  // Case 2: Select of two constants → conditional redirect.
  if (auto *sel = llvm::dyn_cast<llvm::SelectInst>(next_state)) {
    auto *true_ci = llvm::dyn_cast<llvm::ConstantInt>(sel->getTrueValue());
    auto *false_ci = llvm::dyn_cast<llvm::ConstantInt>(sel->getFalseValue());
    if (!true_ci || !false_ci)
      return std::nullopt;

    auto true_it = info.state_to_block.find(true_ci->getSExtValue());
    auto false_it = info.state_to_block.find(false_ci->getSExtValue());
    if (true_it == info.state_to_block.end() ||
        false_it == info.state_to_block.end())
      return std::nullopt;

    return Redirect{src, true_it->second, sel->getCondition(),
                    false_it->second};
  }

  return std::nullopt;
}

/// Apply all collected redirects for a single dispatcher.
///
/// For each target block gaining new predecessors, proxy PHIs are inserted
/// to thread non-state values that previously flowed through the dispatcher.
bool applyRedirects(const DispatcherInfo &info,
                    llvm::ArrayRef<Redirect> redirects) {
  if (redirects.empty())
    return false;

  // Phase 1: Collect new incoming edges per target block.
  //   Maps target → [ (source, { dispatcher_phi → value_from_source }) ]
  using PhiValueMap = llvm::DenseMap<llvm::PHINode *, llvm::Value *>;
  struct IncomingEdge {
    llvm::BasicBlock *from;
    PhiValueMap phi_values;
  };
  llvm::DenseMap<llvm::BasicBlock *,
                 llvm::SmallVector<IncomingEdge, 4>>
      new_edges;

  for (auto &r : redirects) {
    IncomingEdge edge;
    edge.from = r.src;
    for (auto *phi : info.all_phis)
      edge.phi_values[phi] = phi->getIncomingValueForBlock(r.src);
    new_edges[r.true_target].push_back(edge);
    if (r.false_target)
      new_edges[r.false_target].push_back(edge);
  }

  // Phase 2: Create proxy PHIs in target blocks.
  //   Maps (target_block, dispatcher_phi) → proxy PHI.
  llvm::DenseMap<llvm::BasicBlock *,
                 llvm::DenseMap<llvm::PHINode *, llvm::PHINode *>>
      proxies;

  for (auto &[target, sources] : new_edges) {
    for (auto *disp_phi : info.all_phis) {
      if (disp_phi == info.state_phi)
        continue;  // State PHI is only consumed by the switch.
      if (disp_phi->use_empty())
        continue;

      auto *proxy = llvm::PHINode::Create(
          disp_phi->getType(),
          static_cast<unsigned>(1 + sources.size()),
          disp_phi->getName() + ".unflat");
      proxy->insertBefore(target->begin());

      // Existing edge: from the dispatcher.
      proxy->addIncoming(disp_phi, info.block);

      // New edges: from each redirected source.
      for (auto &e : sources)
        proxy->addIncoming(e.phi_values[disp_phi], e.from);

      proxies[target][disp_phi] = proxy;
    }
  }

  // Phase 2.5: Update existing (non-proxy) PHI nodes in target blocks.
  // When a redirect adds r.src as a new predecessor of r.true_target,
  // every PHI in r.true_target needs an incoming value from r.src.
  // Proxy PHIs (created in Phase 2) already have these entries.
  // Existing PHIs that receive values from info.block (the dispatcher)
  // need entries from each redirected source.
  for (auto &[target, sources] : new_edges) {
    for (auto &inst : *target) {
      auto *phi = llvm::dyn_cast<llvm::PHINode>(&inst);
      if (!phi)
        break;
      if (phi->getName().ends_with(".unflat"))
        continue;  // Proxy PHIs already have entries from new sources.

      int disp_idx = phi->getBasicBlockIndex(info.block);
      if (disp_idx < 0)
        continue;
      llvm::Value *val_from_disp = phi->getIncomingValue(disp_idx);

      for (auto &e : sources) {
        llvm::Value *new_val = val_from_disp;
        // If the value is a dispatcher PHI, use the source's contribution
        // to that PHI (which dominates the source block).
        if (auto *dp = llvm::dyn_cast<llvm::PHINode>(val_from_disp)) {
          if (dp->getParent() == info.block)
            new_val = dp->getIncomingValueForBlock(e.from);
        }
        phi->addIncoming(new_val, e.from);
      }
    }
  }

  // Phase 3: In each target block, replace uses of dispatcher PHIs with
  // their proxy PHIs.  This handles values that flow through the dispatcher
  // to the target block.
  for (auto &[target, phi_map] : proxies) {
    for (auto &inst : *target) {
      // Don't rewrite the proxy PHIs themselves.
      if (llvm::isa<llvm::PHINode>(&inst) &&
          inst.getName().ends_with(".unflat"))
        continue;
      for (auto &[disp_phi, proxy] : phi_map)
        inst.replaceUsesOfWith(disp_phi, proxy);
    }
  }

  // Phase 4: Rewrite branch targets and remove entries from dispatcher PHIs.
  for (auto &r : redirects) {
    auto *br = llvm::cast<llvm::BranchInst>(r.src->getTerminator());
    br->eraseFromParent();

    llvm::IRBuilder<> B(r.src);
    if (r.condition)
      B.CreateCondBr(r.condition, r.true_target, r.false_target);
    else
      B.CreateBr(r.true_target);

    // Remove this source from all dispatcher PHIs.
    for (auto *phi : info.all_phis) {
      int idx = phi->getBasicBlockIndex(r.src);
      if (idx >= 0)
        phi->removeIncomingValue(static_cast<unsigned>(idx),
                                 /*DeletePHIIfEmpty=*/false);
    }
  }

  return true;
}

}  // namespace

llvm::PreservedAnalyses ControlFlowUnflattenerPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &FAM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  // Iterate to fixpoint: each successful batch may expose further
  // dispatchers (nested CFF) or simplify existing ones.
  bool progress = true;
  while (progress) {
    progress = false;

    for (auto &BB : F) {
      auto info = identifyDispatcher(&BB);
      if (!info)
        continue;

      // Collect unique switch successors.
      llvm::DenseSet<llvm::BasicBlock *> succ_set;
      for (auto &c : info->sw->cases())
        succ_set.insert(c.getCaseSuccessor());

      // Analyze each switch successor for resolvable back-edges.
      llvm::SmallVector<Redirect, 16> redirects;
      for (auto *succ : succ_set) {
        if (auto r = analyzeBackEdge(succ, *info))
          redirects.push_back(*r);
      }

      if (applyRedirects(*info, redirects)) {
        changed = true;
        progress = true;
        break;  // Restart scan — iterators may be invalidated.
      }
    }
  }

  if (!changed)
    return llvm::PreservedAnalyses::all();

  canonicalizePhiIncomingEdges(F);

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
