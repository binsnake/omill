#include "omill/Analysis/StateFieldAccessAnalysis.h"

#include <llvm/IR/Argument.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Utils/StateFieldMap.h"

namespace omill {

llvm::AnalysisKey StateFieldAccessAnalysis::Key;

namespace {

/// Check if a value derives from the State pointer (first function argument).
bool derivesFromStatePtr(llvm::Value *V) {
  llvm::SmallVector<llvm::Value *, 8> worklist;
  llvm::DenseSet<llvm::Value *> visited;
  worklist.push_back(V);

  while (!worklist.empty()) {
    auto *cur = worklist.pop_back_val();
    if (!visited.insert(cur).second) continue;

    if (auto *arg = llvm::dyn_cast<llvm::Argument>(cur)) {
      if (arg->getArgNo() == 0) return true;
      continue;
    }

    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(cur)) {
      worklist.push_back(GEP->getPointerOperand());
      continue;
    }

    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(cur)) {
      worklist.push_back(BC->getOperand(0));
      continue;
    }

    if (auto *PHI = llvm::dyn_cast<llvm::PHINode>(cur)) {
      for (auto &incoming : PHI->incoming_values()) {
        worklist.push_back(incoming.get());
      }
      continue;
    }
  }

  return false;
}

/// Resolve a pointer to its byte offset from the State base.
/// Returns -1 if not resolvable.
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
      return -1;  // Non-constant GEP offset
    }

    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }

    break;
  }

  // Verify the base is the State pointer
  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }

  return -1;
}

/// Compute basic liveness: is this field read before it's written?
/// This is a simplified analysis that works per-function.
void computeFieldLiveness(
    llvm::Function &F,
    llvm::DenseMap<unsigned, FieldAccessInfo> &fields) {

  // For each field, check if any load dominates all stores.
  // Simple approach: check if the first access in entry block order is a load.
  // A more precise analysis would use dominator trees.

  // Track which fields have been written per basic block path.
  // For now, use a simple heuristic: if the first instruction accessing
  // this field (in entry-block DFS order) is a load, it's live-in.
  // If a field is ever stored, it's potentially live-out.

  llvm::DenseMap<unsigned, bool> first_access_is_load;
  llvm::DenseSet<unsigned> seen;

  // Walk blocks in RPO (entry block first)
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        auto &DL = F.getParent()->getDataLayout();
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0 && !seen.count(static_cast<unsigned>(off))) {
          seen.insert(static_cast<unsigned>(off));
          first_access_is_load[static_cast<unsigned>(off)] = true;
        }
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto &DL = F.getParent()->getDataLayout();
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0 && !seen.count(static_cast<unsigned>(off))) {
          seen.insert(static_cast<unsigned>(off));
          first_access_is_load[static_cast<unsigned>(off)] = false;
        }
      }
    }
  }

  for (auto &[offset, info] : fields) {
    auto it = first_access_is_load.find(offset);
    if (it != first_access_is_load.end()) {
      info.is_live_in = it->second;
    }
    // Conservatively: any field that is stored is potentially live-out.
    info.is_live_out = !info.stores.empty();
  }
}

}  // namespace

StateFieldAccessInfo StateFieldAccessAnalysis::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  StateFieldAccessInfo result;

  auto &DL = F.getParent()->getDataLayout();
  StateFieldMap field_map(*F.getParent());

  // Scan all instructions for loads/stores that access the State struct.
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        llvm::Value *ptr = LI->getPointerOperand();
        if (!derivesFromStatePtr(ptr)) continue;

        int64_t offset = resolveStateOffset(ptr, DL);
        if (offset < 0) continue;

        unsigned off = static_cast<unsigned>(offset);
        unsigned size = static_cast<unsigned>(
            DL.getTypeStoreSize(LI->getType()));

        auto &info = result.fields[off];
        info.offset = off;
        info.size = size;
        info.loads.push_back(LI);
        result.all_state_loads.push_back(LI);

        // Try to get a name
        if (auto field = field_map.fieldAtOffset(off)) {
          info.name = field->name;
        }
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        llvm::Value *ptr = SI->getPointerOperand();
        if (!derivesFromStatePtr(ptr)) continue;

        int64_t offset = resolveStateOffset(ptr, DL);
        if (offset < 0) continue;

        unsigned off = static_cast<unsigned>(offset);
        unsigned size = static_cast<unsigned>(
            DL.getTypeStoreSize(SI->getValueOperand()->getType()));

        auto &info = result.fields[off];
        info.offset = off;
        info.size = size;
        info.stores.push_back(SI);
        result.all_state_stores.push_back(SI);

        if (auto field = field_map.fieldAtOffset(off)) {
          info.name = field->name;
        }
      }
    }
  }

  // Compute liveness
  computeFieldLiveness(F, result.fields);

  // Populate convenience sets
  for (auto &[offset, info] : result.fields) {
    if (info.is_live_in) {
      result.live_in_offsets.insert(offset);
    }
    if (info.is_live_out) {
      result.live_out_offsets.insert(offset);
    }
  }

  return result;
}

}  // namespace omill
