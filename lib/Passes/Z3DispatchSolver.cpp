#if OMILL_ENABLE_Z3

#include "omill/Passes/Z3DispatchSolver.h"

#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include <z3++.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/SouperZ3Translator.h"

#include "JumpTableUtils.h"

namespace omill {

namespace {

/// Maximum number of solutions to enumerate per dispatch target.
static constexpr unsigned kMaxSolutions = 256;

/// Maximum CFG depth for path constraint collection.
static constexpr unsigned kMaxPathDepth = 8;

/// Collect path constraints by walking backward from `target_bb` through
/// the CFG.  For each conditional branch along the path, we add a constraint
/// that the condition holds (or doesn't) depending on which edge leads
/// toward the dispatch block.
void collectPathConstraints(llvm::BasicBlock *target_bb,
                            LLVMZ3Translator &translator,
                            llvm::SmallVectorImpl<z3::expr> &constraints,
                            unsigned max_depth) {
  llvm::SmallPtrSet<llvm::BasicBlock *, 16> visited;
  llvm::SmallVector<std::pair<llvm::BasicBlock *, unsigned>, 16> worklist;
  worklist.push_back({target_bb, 0});

  while (!worklist.empty()) {
    auto [bb, depth] = worklist.pop_back_val();
    if (depth >= max_depth)
      continue;
    if (!visited.insert(bb).second)
      continue;

    for (auto *pred : predecessors(bb)) {
      auto *term = pred->getTerminator();
      auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
      if (!br) {
        worklist.push_back({pred, depth + 1});
        continue;
      }

      if (!br->isConditional()) {
        worklist.push_back({pred, depth + 1});
        continue;
      }

      auto *cond = br->getCondition();
      auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(cond);
      if (!icmp) {
        worklist.push_back({pred, depth + 1});
        continue;
      }

      bool on_true = (br->getSuccessor(0) == bb);

      // Translate the icmp to a Z3 boolean directly.
      z3::expr cond_z3 = translator.translateICmp(icmp);

      if (on_true) {
        constraints.push_back(cond_z3);
      } else {
        constraints.push_back(!cond_z3);
      }

      worklist.push_back({pred, depth + 1});
    }
  }
}

/// Try to resolve a dispatch_jump target using Z3 constraint solving.
/// Returns true if the dispatch was resolved (switch built).
bool solveDispatch(llvm::CallInst *dispatch_call, llvm::ReturnInst *ret,
                   llvm::Function &F, const BinaryMemoryMap &map,
                   const LiftedFunctionMap *lifted) {
  auto *target_val = dispatch_call->getArgOperand(1);
  if (llvm::isa<llvm::ConstantInt>(target_val))
    return false;

  // The target must be an instruction we can walk.
  if (!llvm::isa<llvm::Instruction>(target_val) &&
      !llvm::isa<llvm::Argument>(target_val))
    return false;

  // Set up Z3 solver.
  z3::context ctx;
  ctx.set("timeout", static_cast<int>(5000));  // 5 second timeout per dispatch.
  LLVMZ3Translator translator(ctx);

  z3::expr target_expr = translator.translate(target_val);

  // Collect path constraints.
  llvm::SmallVector<z3::expr, 8> path_constraints;
  collectPathConstraints(dispatch_call->getParent(), translator,
                         path_constraints, kMaxPathDepth);

  z3::solver solver(ctx);

  // Add path constraints.
  for (auto &pc : path_constraints)
    solver.add(pc);

  // Add address range bound: target must be a reasonable code address.
  // Non-zero, within 48-bit address space (Windows user-mode limit).
  solver.add(target_expr != ctx.bv_val(0, 64));
  solver.add(z3::ult(target_expr, ctx.bv_val(0x800000000000ULL, 64)));

  // Enumerate solutions.
  llvm::SmallVector<uint64_t, 32> solutions;
  while (solver.check() == z3::sat && solutions.size() < kMaxSolutions) {
    auto model = solver.get_model();
    z3::expr val = model.eval(target_expr, true);

    uint64_t solution = 0;
    if (val.is_numeral()) {
      solution = val.get_numeral_uint64();
    } else {
      break;
    }

    solutions.push_back(solution);

    // Block this solution.
    solver.add(target_expr != ctx.bv_val(solution, 64));
  }

  if (solutions.empty())
    return false;

  // If too many solutions, the problem is likely underconstrained.
  if (solutions.size() >= kMaxSolutions)
    return false;

  // Filter solutions to valid targets.
  struct CaseTarget {
    uint64_t index;
    llvm::BasicBlock *target_bb;
  };
  llvm::SmallVector<CaseTarget, 32> cases;
  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *BB = dispatch_call->getParent();

  for (uint64_t i = 0; i < solutions.size(); ++i) {
    uint64_t target_va = solutions[i];

    // Try intra-function block.
    if (auto *target_bb = findBlockForPC(F, target_va)) {
      cases.push_back({i, target_bb});
      continue;
    }

    // Try inter-function tail call.
    auto *target_fn = lifted ? lifted->lookup(target_va) : nullptr;
    if (target_fn) {
      char name[64];
      snprintf(name, sizeof(name), "z3_case_%llu",
               (unsigned long long)i);
      auto *trampoline = llvm::BasicBlock::Create(Ctx, name, &F);
      llvm::IRBuilder<> TBuilder(trampoline);

      auto *state = dispatch_call->getArgOperand(0);
      auto *pc_val = llvm::ConstantInt::get(i64_ty, target_va);
      auto *mem = dispatch_call->getArgOperand(2);

      auto *tail = TBuilder.CreateCall(target_fn, {state, pc_val, mem});
      tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
      TBuilder.CreateRet(tail);

      cases.push_back({i, trampoline});
      continue;
    }

    // Solution is not a valid target — skip it.
  }

  if (cases.empty())
    return false;

  // Build switch on the target value — each case matches a resolved address.
  llvm::BasicBlock *default_bb = nullptr;
  if (cases.size() < solutions.size()) {
    default_bb = llvm::BasicBlock::Create(Ctx, "z3_default", &F);
    llvm::IRBuilder<> DBuilder(default_bb);
    auto *dispatch_fn = dispatch_call->getCalledFunction();
    auto *new_call = DBuilder.CreateCall(
        dispatch_fn,
        {dispatch_call->getArgOperand(0),
         dispatch_call->getArgOperand(1),
         dispatch_call->getArgOperand(2)});
    DBuilder.CreateRet(new_call);
  } else {
    default_bb = llvm::BasicBlock::Create(Ctx, "z3_default", &F);
    new llvm::UnreachableInst(Ctx, default_bb);
  }

  // Save old successors for PHI cleanup.
  llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

  // Build switch.
  llvm::IRBuilder<> Builder(dispatch_call);
  auto *sw = Builder.CreateSwitch(dispatch_call->getArgOperand(1),
                                  default_bb, cases.size());
  for (auto &c : cases)
    sw->addCase(llvm::ConstantInt::get(i64_ty, solutions[c.index]),
                c.target_bb);

  // Erase original dispatch_jump + ret.
  dispatch_call->replaceAllUsesWith(
      llvm::PoisonValue::get(dispatch_call->getType()));
  ret->eraseFromParent();
  dispatch_call->eraseFromParent();

  // Clean up dead instructions after switch.
  while (&BB->back() != sw) {
    auto &dead = BB->back();
    if (!dead.use_empty())
      dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
    dead.eraseFromParent();
  }

  // Update PHI nodes for removed predecessors.
  llvm::SmallPtrSet<llvm::BasicBlock *, 16> new_succs(
      successors(BB).begin(), successors(BB).end());
  for (auto *old_succ : old_succs)
    if (!new_succs.count(old_succ))
      old_succ->removePredecessor(BB);

  return true;
}

}  // namespace

llvm::PreservedAnalyses Z3DispatchSolverPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  // Find unresolved dispatch_jump candidates.
  struct Candidate {
    llvm::CallInst *dispatch_call;
    llvm::ReturnInst *ret;
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
      if (llvm::isa<llvm::ConstantInt>(call->getArgOperand(1)))
        continue;

      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      if (!ret)
        continue;

      candidates.push_back({call, ret});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &cand : candidates) {
    if (solveDispatch(cand.dispatch_call, cand.ret, F, *map, lifted))
      changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#endif  // OMILL_ENABLE_Z3
