#if OMILL_ENABLE_SOUPER

#include "omill/Passes/Z3DispatchSolver.h"

#include <llvm/IR/CFG.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/raw_ostream.h>

#include <souper/Extractor/Candidates.h>
#include <souper/Inst/Inst.h>

#include <z3++.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/SouperZ3Translator.h"

#include "JumpTableUtils.h"

namespace omill {

namespace {

using namespace llvm::PatternMatch;

/// Maximum number of solutions to enumerate per dispatch target.
static constexpr unsigned kMaxSolutions = 256;

/// Maximum recursion depth for variable resolution.
static constexpr unsigned kMaxRecursionDepth = 4;

/// Maximum CFG depth for path constraint collection.
static constexpr unsigned kMaxPathDepth = 8;

/// Collect path constraints by walking backward from `target_bb` through
/// the CFG.  For each conditional branch along the path, we add a constraint
/// that the condition holds (or doesn't) depending on which edge leads
/// toward the dispatch block.
///
/// Returns Z3 boolean expressions representing the conjunction of all
/// branch conditions on the path.
void collectPathConstraints(
    llvm::BasicBlock *target_bb, z3::context &ctx,
    SouperZ3Translator &translator,
    souper::ExprBuilderContext &expr_ctx,
    souper::InstContext &inst_ctx,
    llvm::SmallVectorImpl<z3::expr> &constraints, unsigned max_depth) {
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
      bool on_true = (br->getSuccessor(0) == bb);

      // Try to find the condition in Souper's expression context.
      auto cond_it = expr_ctx.InstMap.find(cond);
      if (cond_it == expr_ctx.InstMap.end()) {
        worklist.push_back({pred, depth + 1});
        continue;
      }

      souper::Inst *cond_inst = cond_it->second;
      z3::expr cond_z3 = translator.translate(cond_inst);

      // Condition is a 1-bit bitvector.  on_true => cond == 1.
      if (on_true) {
        constraints.push_back(cond_z3 == ctx.bv_val(1, 1));
      } else {
        constraints.push_back(cond_z3 == ctx.bv_val(0, 1));
      }

      worklist.push_back({pred, depth + 1});
    }
  }
}

/// Try to resolve a dispatch_jump target using Z3 constraint solving.
/// Returns true if the dispatch was resolved (switch built).
bool solveDispatch(llvm::CallInst *dispatch_call, llvm::ReturnInst *ret,
                   llvm::Function &F, const BinaryMemoryMap &map,
                   const LiftedFunctionMap *lifted,
                   souper::InstContext &inst_ctx,
                   souper::ExprBuilderContext &expr_ctx,
                   unsigned recursion_depth) {
  if (recursion_depth > kMaxRecursionDepth)
    return false;

  auto *target_val = dispatch_call->getArgOperand(1);
  if (llvm::isa<llvm::ConstantInt>(target_val))
    return false;

  // Look up the target in Souper's expression map.
  auto target_it = expr_ctx.InstMap.find(target_val);
  if (target_it == expr_ctx.InstMap.end())
    return false;

  souper::Inst *target_inst = target_it->second;

  // Set up Z3 solver.
  z3::context ctx;
  ctx.set("timeout", 5000u);  // 5 second timeout per dispatch.
  SouperZ3Translator translator(ctx);

  z3::expr target_expr = translator.translate(target_inst);

  // Collect path constraints.
  llvm::SmallVector<z3::expr, 8> path_constraints;
  collectPathConstraints(dispatch_call->getParent(), ctx, translator,
                         expr_ctx, inst_ctx, path_constraints, kMaxPathDepth);

  z3::solver solver(ctx);

  // Add path constraints.
  for (auto &pc : path_constraints)
    solver.add(pc);

  // Add address range bound: target must be a reasonable code address.
  // Use the binary memory map's regions to determine bounds.
  // For now, use a conservative check: target must be non-zero and
  // within 48-bit address space (Windows user-mode limit).
  solver.add(target_expr != ctx.bv_val(0, 64));
  solver.add(z3::ult(target_expr, ctx.bv_val(0x800000000000ULL, 64)));

  // Enumerate solutions.
  llvm::SmallVector<uint64_t, 32> solutions;
  while (solver.check() == z3::sat && solutions.size() < kMaxSolutions) {
    auto model = solver.get_model();
    z3::expr val = model.eval(target_expr, true);

    uint64_t solution = 0;
    if (val.is_numeral()) {
      // Z3 C++ API: get_numeral_uint64 for bitvectors.
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

  // Build switch.  We use a synthetic index that maps each solution to a
  // case.  The switch discriminant is the target value itself.
  llvm::BasicBlock *default_bb = nullptr;
  if (cases.size() < solutions.size()) {
    // Not all solutions resolved — keep a default dispatch.
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

  // Build switch on the target value directly — each case matches
  // a specific resolved address.
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

  // Build Souper expression context for the function.
  souper::InstContext inst_ctx;
  souper::ExprBuilderContext expr_ctx;
  souper::ExprBuilderOptions opts;
  opts.NamedArrays = false;

  // Extract candidates from the function.
  // This builds the InstMap that maps LLVM Values → Souper Inst DAGs.
  auto candidate_set = souper::ExtractCandidates(F, inst_ctx, expr_ctx, opts);

  bool changed = false;

  for (auto &cand : candidates) {
    if (solveDispatch(cand.dispatch_call, cand.ret, F, *map, lifted,
                      inst_ctx, expr_ctx, /*recursion_depth=*/0)) {
      changed = true;
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill

#endif  // OMILL_ENABLE_SOUPER
