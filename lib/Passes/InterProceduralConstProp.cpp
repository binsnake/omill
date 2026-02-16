#include "omill/Passes/InterProceduralConstProp.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/CallGraphAnalysis.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

/// Win64 parameter register offsets (same as CallingConventionAnalysis).
static constexpr const char *kWin64ParamRegs[] = {"RCX", "RDX", "R8", "R9"};

/// Resolve a pointer value to its byte offset into the State struct.
/// Returns -1 if not resolvable to State.
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

/// Pre-call constants: for each State field offset, the ConstantInt stored.
using PreCallConstants = llvm::DenseMap<unsigned, llvm::ConstantInt *>;

/// Collect constant stores to parameter register offsets in the same
/// basic block before the call instruction, walking backwards.
PreCallConstants collectPreCallConstants(
    llvm::CallInst *CI, const llvm::DataLayout &DL,
    const llvm::DenseSet<unsigned> &param_offsets) {
  PreCallConstants result;
  llvm::DenseSet<unsigned> seen_offsets;

  // Walk backwards from the call instruction in the same basic block.
  auto *BB = CI->getParent();
  auto it = CI->getIterator();

  while (it != BB->begin()) {
    --it;
    auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it);
    if (!SI) continue;

    int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
    if (off < 0) continue;

    unsigned u = static_cast<unsigned>(off);
    if (!param_offsets.count(u)) continue;
    if (seen_offsets.count(u)) continue;  // first store wins (closest to call)

    seen_offsets.insert(u);

    if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand())) {
      result[u] = C;
    }
    // Non-constant store → mark offset as seen but don't add to result,
    // which means this offset can't be unanimously constant.
  }

  return result;
}

/// For a given function, replace loads from State at the given offset
/// in the entry block with the constant. Returns true if any replacement made.
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

    // Type must match.
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

llvm::PreservedAnalyses InterProceduralConstPropPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &call_graph = MAM.getResult<CallGraphAnalysis>(M);
  auto &DL = M.getDataLayout();

  // Build the set of Win64 parameter offsets.
  StateFieldMap field_map(M);
  llvm::DenseSet<unsigned> param_offsets;
  llvm::DenseMap<unsigned, llvm::Type *> param_types;

  for (auto *reg_name : kWin64ParamRegs) {
    if (auto field = field_map.fieldByName(reg_name)) {
      param_offsets.insert(field->offset);
    }
  }

  if (param_offsets.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  bool changed = false;

  // Process functions bottom-up via SCC order.
  for (auto &scc : call_graph.getBottomUpSCCs()) {
    // Skip non-trivial SCCs (mutual recursion) — conservative.
    if (scc.size() != 1) continue;

    auto *F = scc[0];
    auto *node = call_graph.getNode(F);
    if (!node) continue;

    // Skip functions with no callers (entry points).
    if (node->callers.empty()) continue;

    // Skip functions with unresolved callers.
    bool has_unresolved_caller = false;
    for (auto *caller_cs : node->callers) {
      auto *caller_node = call_graph.getNode(caller_cs->caller);
      if (!caller_node || caller_node->unresolved_count > 0) {
        has_unresolved_caller = true;
        break;
      }
    }
    if (has_unresolved_caller) continue;

    // For each parameter offset, check if all callers agree on a constant.
    for (unsigned offset : param_offsets) {
      llvm::ConstantInt *unanimous = nullptr;
      bool all_agree = true;

      for (auto *caller_cs : node->callers) {
        auto pre_call = collectPreCallConstants(
            caller_cs->inst, DL, param_offsets);

        auto it = pre_call.find(offset);
        if (it == pre_call.end()) {
          all_agree = false;
          break;
        }

        if (!unanimous) {
          unanimous = it->second;
        } else if (unanimous->getValue() != it->second->getValue()) {
          all_agree = false;
          break;
        }
      }

      if (all_agree && unanimous) {
        changed |= replaceEntryBlockLoads(*F, offset, unanimous, DL);
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
