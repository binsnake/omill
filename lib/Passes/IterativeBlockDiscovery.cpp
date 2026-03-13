#include "omill/Passes/IterativeBlockDiscovery.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>

#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Prefix used by BlockLifter for block-function names.
static constexpr const char *kBlockPrefix = "blk_";

/// Check if a function is a block-function.
bool isBlockFunction(const llvm::Function &F) {
  return F.getName().starts_with(kBlockPrefix) && !F.isDeclaration();
}

bool isDiscoveryFunction(const llvm::Function &F) {
  return isBlockFunction(F) || isLiftedFunction(F);
}

std::optional<uint64_t> parseBlockAddr(const llvm::Function &F) {
  auto name = F.getName();
  if (!name.starts_with(kBlockPrefix))
    return std::nullopt;

  uint64_t addr = 0;
  if (name.drop_front(4).getAsInteger(16, addr))
    return std::nullopt;
  return addr;
}

std::optional<uint64_t> parseDiscoveryAddr(const llvm::Function &F) {
  if (auto addr = parseBlockAddr(F))
    return addr;
  if (isLiftedFunction(F))
    return extractEntryVA(F.getName());
  return std::nullopt;
}

void recordBlockGraphState(llvm::Module &M, IterativeLiftingSession &session) {
  for (auto &F : M) {
    if (!isDiscoveryFunction(F))
      continue;

    auto source_pc = parseDiscoveryAddr(F);
    if (!source_pc)
      continue;

    session.noteLiftedTarget(*source_pc);
    llvm::SmallVector<LiftEdge, 8> outgoing;

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;

        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;

        LiftEdge edge;
        edge.source_pc = *source_pc;

        if (callee->getName() == "__omill_dispatch_jump" ||
            callee->getName() == "__omill_dispatch_call") {
          edge.kind = (callee->getName() == "__omill_dispatch_call")
                          ? LiftEdgeKind::kIndirectCall
                          : LiftEdgeKind::kIndirectBranch;
          if (call->arg_size() >= 2) {
            if (auto *pc_arg =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              edge.target_pc = pc_arg->getZExtValue();
            }
          }
          edge.resolved = false;
          outgoing.push_back(edge);
          if (edge.target_pc != 0)
            session.queueTarget(edge.target_pc);
          continue;
        }

        if (auto target_pc = parseDiscoveryAddr(*callee)) {
          edge.kind = isBlockFunction(*callee) ? LiftEdgeKind::kDirectBranch
                                               : LiftEdgeKind::kDirectCall;
          edge.target_pc = *target_pc;
          edge.resolved = true;
          session.noteLiftedTarget(*target_pc);
          outgoing.push_back(edge);
        }
      }
    }

    session.graph().syncOutgoingEdges(*source_pc, outgoing);
  }
}

/// Collect all constant dispatch target PCs from block-functions.
/// Returns PCs where no corresponding blk_<hex> definition exists.
llvm::DenseSet<uint64_t> collectNewTargetPCs(llvm::Module &M) {
  llvm::DenseSet<uint64_t> new_pcs;
  for (auto &F : M) {
    if (!isDiscoveryFunction(F))
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name != "__omill_dispatch_jump" && name != "__omill_dispatch_call")
          continue;
        if (call->arg_size() < 2)
          continue;
        auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!pc_arg)
          continue;
        uint64_t target_pc = pc_arg->getZExtValue();
        if (target_pc == 0)
          continue;
        // Check if a block-function already exists for this target.
        char target_name[64];
        snprintf(target_name, sizeof(target_name), "blk_%llx",
                 (unsigned long long)target_pc);
        auto *target_fn = M.getFunction(target_name);
        if (!target_fn || target_fn->isDeclaration())
          new_pcs.insert(target_pc);
      }
    }
  }
  return new_pcs;
}

/// Count the total number of unresolved dispatch calls in block-functions.
unsigned countUnresolvedBlockDispatches(llvm::Module &M) {
  unsigned count = 0;
  for (auto &F : M) {
    if (!isDiscoveryFunction(F))
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name == "__omill_dispatch_call" || name == "__omill_dispatch_jump")
          ++count;
      }
    }
  }
  return count;
}

/// Replace dispatch calls that have a constant target PC and the callee
/// exists as a block-function with a musttail call to that block-function.
/// This "resolves" the dispatch into a direct block-to-block edge.
bool resolveConstantDispatches(llvm::Module &M) {
  bool changed = false;
  llvm::SmallVector<std::pair<llvm::CallInst *, llvm::Function *>, 16>
      to_replace;

  for (auto &F : M) {
    if (!isDiscoveryFunction(F))
      continue;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee)
          continue;
        auto name = callee->getName();
        if (name != "__omill_dispatch_jump" && name != "__omill_dispatch_call")
          continue;

        // Check if PC argument is constant.
        if (call->arg_size() < 2)
          continue;
        auto *pc_arg =
            llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!pc_arg)
          continue;
        uint64_t target_pc = pc_arg->getZExtValue();
        if (target_pc == 0)
          continue;

        // Find the corresponding block-function.
        char target_name[64];
        snprintf(target_name, sizeof(target_name), "blk_%llx",
                 (unsigned long long)target_pc);
        auto *target_fn = M.getFunction(target_name);
        if (!target_fn || target_fn->isDeclaration())
          continue;

        to_replace.push_back({call, target_fn});
      }
    }
  }

  for (auto &[call, target_fn] : to_replace) {
    // The dispatch call pattern is:
    //   %r = call @__omill_dispatch_jump(state, pc, mem)
    //   ret %r
    // Replace with:
    //   %r = musttail call @blk_xxx(state, pc, mem)
    //   ret %r

    // Only use musttail if the call is in strict tail position:
    // the call's only user must be a ReturnInst and the call and ret
    // must be the last two instructions in the block.
    bool can_musttail = false;
    if (call->hasOneUse()) {
      auto *user = call->user_back();
      if (auto *ret = llvm::dyn_cast<llvm::ReturnInst>(user)) {
        if (ret->getParent() == call->getParent() &&
            &call->getParent()->back() == ret) {
          can_musttail = true;
        }
      }
    }

    auto *new_call = llvm::CallInst::Create(
        target_fn->getFunctionType(), target_fn,
        {call->getArgOperand(0), call->getArgOperand(1),
         call->getArgOperand(2)},
        "", call->getIterator());
    if (can_musttail)
      new_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    call->replaceAllUsesWith(new_call);
    call->eraseFromParent();
    changed = true;
  }

  return changed;
}

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

}  // namespace

llvm::PreservedAnalyses IterativeBlockDiscoveryPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &session_result = MAM.getResult<IterativeLiftingSessionAnalysis>(M);
  auto session = session_result.session;

  // Check if there are any block-functions to process.
  bool has_block_fns = false;
  for (auto &F : M) {
    if (isBlockFunction(F)) {
      has_block_fns = true;
      break;
    }
  }
  if (!has_block_fns)
    return llvm::PreservedAnalyses::all();

  if (session)
    recordBlockGraphState(M, *session);

  unsigned prev_unresolved = countUnresolvedBlockDispatches(M);
  if (prev_unresolved == 0)
    return llvm::PreservedAnalyses::all();

  // Try to get the block-lifting callback.  If registered, we can lift
  // new blocks at PCs discovered during optimization.  If not registered,
  // we can only resolve dispatches to existing block-functions.
  BlockLiftCallback lift_block;
  lift_block = MAM.getResult<BlockLiftAnalysis>(M).lift_block;

  bool ever_changed = false;
  unsigned iteration = 0;

  do {
    auto dirty_before = session ? session->graph().dirtyNodes().size() : 0u;
    // Step 1: Run lightweight optimization on all block-functions.
    {
      llvm::FunctionPassManager FPM;
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(ConstantMemoryFoldingPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(llvm::SimplifyCFGPass());
      auto adaptor = llvm::createModuleToFunctionPassAdaptor(std::move(FPM));
      adaptor.run(M, MAM);
    }

    // Step 2: If we have a lift callback, discover new target PCs and
    // lift blocks that don't exist yet.
    if (lift_block) {
      auto new_pcs = collectNewTargetPCs(M);
      for (uint64_t pc : new_pcs) {
        if (session)
          session->queueTarget(pc);
        if (lift_block(pc)) {
          if (session)
            session->noteLiftedTarget(pc);
          ever_changed = true;
        }
      }
    }

    // Step 3: Resolve dispatch calls with constant targets.
    bool resolved = resolveConstantDispatches(M);
    if (resolved)
      ever_changed = true;

    if (resolved) {
      for (auto &F : M) {
        if (!isDiscoveryFunction(F))
          continue;
        canonicalizePhiIncomingEdges(F);
      }
    }

    if (session)
      recordBlockGraphState(M, *session);

    unsigned curr_unresolved = countUnresolvedBlockDispatches(M);
    if (session) {
      IterativeRoundSummary summary;
      summary.pipeline = "block";
      summary.iteration = iteration;
      summary.dirty_functions = static_cast<unsigned>(dirty_before);
      summary.unresolved_before = prev_unresolved;
      summary.unresolved_after = curr_unresolved;
      summary.new_targets = 0;
      summary.lifted_new = ever_changed;
      summary.stalled = curr_unresolved >= prev_unresolved;
      session->recordRoundSummary(std::move(summary));
    }
    if (curr_unresolved < prev_unresolved)
      ever_changed = true;

    // Fixed point: no more dispatches resolved.
    if (curr_unresolved >= prev_unresolved)
      break;

    prev_unresolved = curr_unresolved;
    ++iteration;
  } while (iteration < max_iterations_);

  return ever_changed ? llvm::PreservedAnalyses::none()
                      : llvm::PreservedAnalyses::all();
}

}  // namespace omill
