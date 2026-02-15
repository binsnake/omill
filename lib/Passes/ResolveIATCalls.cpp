#include "omill/Passes/ResolveIATCalls.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Check if a condition is known true/false at a basic block by walking
/// up through single-predecessor chains.
bool isConditionKnown(llvm::Value *cond, llvm::BasicBlock *BB,
                      bool &known_val, unsigned depth = 0) {
  if (depth > 8)
    return false;
  for (auto *pred : llvm::predecessors(BB)) {
    auto *br = llvm::dyn_cast<llvm::BranchInst>(pred->getTerminator());
    if (!br || !br->isConditional() || br->getCondition() != cond)
      continue;
    known_val = (br->getSuccessor(0) == BB);
    return true;
  }
  if (auto *pred = BB->getSinglePredecessor())
    return isConditionKnown(cond, pred, known_val, depth + 1);
  return false;
}

/// Recursively evaluate an integer expression to collect all possible
/// concrete values.  Uses branch context to resolve selects when possible.
///
/// @param val       The SSA value to evaluate.
/// @param pc_arg    The function's program_counter argument (may be nullptr
///                  if already folded to constant).
/// @param entry_va  The function's entry virtual address.
/// @param ctx_bb    Basic block of the dispatch_call (for select disambiguation).
/// @param results   Output: all possible concrete values.
/// @param depth     Recursion depth guard.
void collectPossibleValues(llvm::Value *val, llvm::Value *pc_arg,
                           int64_t entry_va, llvm::BasicBlock *ctx_bb,
                           llvm::SmallVectorImpl<uint64_t> &results,
                           unsigned depth = 0) {
  if (depth > 10 || results.size() > 32)
    return;

  // program_counter argument → substitute with entry_va.
  if (pc_arg && val == pc_arg) {
    results.push_back(static_cast<uint64_t>(entry_va));
    return;
  }

  // Constant integer.
  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(val)) {
    results.push_back(ci->getZExtValue());
    return;
  }

  // add(X, Y).
  if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(val)) {
    if (bin->getOpcode() == llvm::Instruction::Add) {
      llvm::SmallVector<uint64_t, 4> lhs, rhs;
      collectPossibleValues(bin->getOperand(0), pc_arg, entry_va, ctx_bb,
                            lhs, depth + 1);
      collectPossibleValues(bin->getOperand(1), pc_arg, entry_va, ctx_bb,
                            rhs, depth + 1);
      for (uint64_t l : lhs)
        for (uint64_t r : rhs)
          results.push_back(l + r);
      return;
    }
  }

  // select(cond, A, B) — try to resolve via branch context.
  if (auto *sel = llvm::dyn_cast<llvm::SelectInst>(val)) {
    bool cond_val;
    if (ctx_bb && isConditionKnown(sel->getCondition(), ctx_bb, cond_val)) {
      // Condition is known at this point — follow only the active arm.
      auto *arm = cond_val ? sel->getTrueValue() : sel->getFalseValue();
      collectPossibleValues(arm, pc_arg, entry_va, ctx_bb, results, depth + 1);
    } else {
      // Unknown condition — try both arms.
      collectPossibleValues(sel->getTrueValue(), pc_arg, entry_va, ctx_bb,
                            results, depth + 1);
      collectPossibleValues(sel->getFalseValue(), pc_arg, entry_va, ctx_bb,
                            results, depth + 1);
    }
    return;
  }
}

/// Try to find a unique IAT import for a dispatch_call.
const BinaryMemoryMap::ImportEntry *
resolveIATTarget(llvm::CallInst *call, uint64_t entry_va,
                 const BinaryMemoryMap &map) {
  auto *load = llvm::dyn_cast<llvm::LoadInst>(call->getArgOperand(1));
  if (!load)
    return nullptr;

  // Get the integer value cast to a pointer for the load address.
  llvm::Value *int_val = nullptr;
  llvm::Value *ptr = load->getPointerOperand()->stripPointerCasts();

  if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
    int_val = itp->getOperand(0);
  else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (ce->getOpcode() == llvm::Instruction::IntToPtr)
      int_val = ce->getOperand(0);
  }

  if (!int_val)
    return nullptr;

  llvm::Function *F = call->getFunction();
  llvm::Value *pc_arg = (F->arg_size() >= 2) ? F->getArg(1) : nullptr;
  llvm::BasicBlock *ctx_bb = call->getParent();

  llvm::SmallVector<uint64_t, 4> addrs;
  collectPossibleValues(int_val, pc_arg, static_cast<int64_t>(entry_va),
                        ctx_bb, addrs);

  if (addrs.empty())
    return nullptr;

  // Find unique matching IAT import.
  const BinaryMemoryMap::ImportEntry *match = nullptr;
  for (uint64_t addr : addrs) {
    auto *imp = map.lookupImport(addr);
    if (!imp)
      continue;
    if (!match) {
      match = imp;
    } else if (match != imp) {
      return nullptr;  // Ambiguous.
    }
  }

  return match;
}

}  // namespace

llvm::PreservedAnalyses ResolveIATCallsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || !map->hasImports())
    return llvm::PreservedAnalyses::all();

  uint64_t entry_va = extractEntryVA(F.getName());
  if (entry_va == 0)
    return llvm::PreservedAnalyses::all();

  struct Candidate {
    llvm::CallInst *call;
    const BinaryMemoryMap::ImportEntry *import;
  };
  llvm::SmallVector<Candidate, 4> candidates;

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

      auto *import = resolveIATTarget(call, entry_va, *map);
      if (!import)
        continue;

      candidates.push_back({call, import});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  for (auto &[call, import] : candidates) {
    auto *fn_type = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
    auto fn_callee = M.getOrInsertFunction(import->function, fn_type);
    auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
    if (!fn)
      continue;
    fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);

    llvm::IRBuilder<> Builder(call);
    auto *fn_addr = Builder.CreatePtrToInt(fn, Builder.getInt64Ty(),
                                           import->function + ".addr");
    call->setArgOperand(1, fn_addr);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
