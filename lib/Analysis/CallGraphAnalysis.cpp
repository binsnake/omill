#include "omill/Analysis/CallGraphAnalysis.h"

#include <llvm/ADT/SCCIterator.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

llvm::AnalysisKey CallGraphAnalysis::Key;

namespace {

/// Simple adjacency-list graph adapter for llvm::scc_iterator.
/// Wraps the LiftedCallGraph nodes so Tarjan's SCC can traverse them.
struct CallGraphAdapter {
  using NodeRef = llvm::Function *;
  using ChildIteratorType = llvm::SmallVector<llvm::Function *, 4>::iterator;

  LiftedCallGraph *graph;

  struct ChildRange {
    llvm::SmallVector<llvm::Function *, 4> children;
    auto begin() { return children.begin(); }
    auto end() { return children.end(); }
  };
};

/// Tarjan's SCC on a simple adjacency list.
/// We implement our own because llvm::scc_iterator requires GraphTraits,
/// which is complex to adapt for our mutable DenseMap-based graph.
class TarjanSCC {
 public:
  using SCCList = llvm::SmallVector<llvm::SmallVector<llvm::Function *, 4>, 16>;

  SCCList compute(
      llvm::DenseMap<const llvm::Function *, CallGraphNode> &nodes,
      LiftedCallGraph &graph) {
    SCCList result;
    index_ = 0;

    for (auto &[func, node] : nodes) {
      if (index_map_.find(func) == index_map_.end()) {
        strongconnect(const_cast<llvm::Function *>(func), graph, result);
      }
    }

    return result;
  }

 private:
  void strongconnect(llvm::Function *v, LiftedCallGraph &graph,
                     SCCList &result) {
    index_map_[v] = index_;
    lowlink_map_[v] = index_;
    index_++;
    stack_.push_back(v);
    on_stack_.insert(v);

    auto *node = graph.getNode(v);
    if (node) {
      for (auto &cs : node->callees) {
        if (!cs.callee) continue;  // skip unresolved

        auto it = index_map_.find(cs.callee);
        if (it == index_map_.end()) {
          strongconnect(cs.callee, graph, result);
          lowlink_map_[v] =
              std::min(lowlink_map_[v], lowlink_map_[cs.callee]);
        } else if (on_stack_.count(cs.callee)) {
          lowlink_map_[v] =
              std::min(lowlink_map_[v], index_map_[cs.callee]);
        }
      }
    }

    if (lowlink_map_[v] == index_map_[v]) {
      llvm::SmallVector<llvm::Function *, 4> scc;
      llvm::Function *w;
      do {
        w = stack_.back();
        stack_.pop_back();
        on_stack_.erase(w);
        scc.push_back(w);
      } while (w != v);
      result.push_back(std::move(scc));
    }
  }

  unsigned index_ = 0;
  llvm::DenseMap<const llvm::Function *, unsigned> index_map_;
  llvm::DenseMap<const llvm::Function *, unsigned> lowlink_map_;
  llvm::SmallVector<llvm::Function *, 16> stack_;
  llvm::DenseSet<const llvm::Function *> on_stack_;
};

}  // namespace

LiftedCallGraph CallGraphAnalysis::run(llvm::Module &M,
                                       llvm::ModuleAnalysisManager &MAM) {
  auto &lifted_map = MAM.getResult<LiftedFunctionAnalysis>(M);
  LiftedCallGraph graph;

  // Step 1: Create nodes for all lifted functions.
  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;
    auto &node = graph.nodes_[&F];
    node.func = &F;
  }

  // Step 2: Scan each lifted function for call sites.
  for (auto &[func_ptr, node] : graph.nodes_) {
    auto *F = node.func;

    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI) continue;

        auto *called = CI->getCalledFunction();
        if (!called) continue;

        llvm::StringRef name = called->getName();

        // Direct call to a lifted function (sub_*)
        if (isLiftedFunction(*called)) {
          CallSite cs;
          cs.inst = CI;
          cs.caller = F;
          cs.callee = called;
          cs.target_pc = extractEntryVA(called->getName());
          cs.is_tail_call = CI->isMustTailCall();
          cs.is_dispatch = false;
          node.callees.push_back(cs);
          continue;
        }

        // __omill_dispatch_call or __omill_dispatch_jump
        if (name == "__omill_dispatch_call" ||
            name == "__omill_dispatch_jump") {
          CallSite cs;
          cs.inst = CI;
          cs.caller = F;
          cs.callee = nullptr;
          cs.target_pc = 0;
          cs.is_tail_call = CI->isMustTailCall();
          cs.is_dispatch = true;

          // Check if target (arg 1) is a constant.
          if (auto *target_ci =
                  llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1))) {
            uint64_t pc = target_ci->getZExtValue();
            cs.target_pc = pc;

            // Try to resolve via lifted function map.
            if (auto *target_fn = lifted_map.lookup(pc)) {
              cs.callee = target_fn;
            }
          }

          // Check for ptrtoint(@dllimport) pattern — external, skip edge.
          if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(
                  CI->getArgOperand(1))) {
            if (ce->getOpcode() == llvm::Instruction::PtrToInt) {
              // External import — don't add to graph.
              continue;
            }
          }

          if (!cs.callee) {
            node.unresolved_count++;
            graph.total_unresolved_++;
          }

          node.callees.push_back(cs);
          continue;
        }
      }
    }
  }

  // Step 3: Build reverse edges (callers).
  for (auto &[func_ptr, node] : graph.nodes_) {
    for (auto &cs : node.callees) {
      if (!cs.callee) continue;
      auto *callee_node = graph.getNode(cs.callee);
      if (callee_node) {
        callee_node->callers.push_back(&cs);
      }
    }
  }

  // Step 4: Compute SCCs bottom-up via Tarjan's algorithm.
  TarjanSCC tarjan;
  graph.sccs_ = tarjan.compute(graph.nodes_, graph);
  // Tarjan's produces SCCs in reverse topological order (roots first),
  // but we want bottom-up (leaves first), which is the default output.
  // Actually, Tarjan's naturally produces leaves first — the first SCC
  // finished is a leaf. So the order is already bottom-up.

  return graph;
}

}  // namespace omill
