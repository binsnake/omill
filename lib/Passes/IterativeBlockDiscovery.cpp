#include "omill/Passes/IterativeBlockDiscovery.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/Scalar/SROA.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/Passes/ConstantMemoryFolding.h"
#include "omill/Passes/CombinedFixedPointDevirt.h"
#include "omill/Passes/FoldProgramCounter.h"
#include "omill/Passes/LowerRemillIntrinsics.h"
#include "omill/Passes/RecoverStackFrame.h"
#include "omill/Passes/InterProceduralConstProp.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Prefixes used by BlockLifter for block-function names.  Plain block
/// bodies use `blk_<pc>`; function entry points (direct call targets and
/// top-level LiftReachable entries) use `sub_<pc>`.  Both carry the
/// `omill.block_lifter` function attribute so we never conflate them
/// with TraceLifter-produced `sub_<pc>` functions that may live in the
/// same module during late-stage cleanup.
static constexpr const char *kBlockPrefix = "blk_";
static constexpr const char *kSubPrefix = "sub_";
static constexpr const char *kBlockLifterAttr = "omill.block_lifter";

/// Check if a function is a block-function produced by BlockLifter.
bool isBlockFunction(const llvm::Function &F) {
  if (F.isDeclaration() || !F.hasFnAttribute(kBlockLifterAttr))
    return false;
  auto name = F.getName();
  return name.starts_with(kBlockPrefix) || name.starts_with(kSubPrefix);
}

bool isDiscoveryFunction(const llvm::Function &F) {
  return isBlockFunction(F) || isLiftedFunction(F);
}

std::optional<uint64_t> parseBlockAddr(const llvm::Function &F) {
  auto name = F.getName();
  llvm::StringRef rest;
  if (name.starts_with(kBlockPrefix))
    rest = name.drop_front(4);
  else if (name.starts_with(kSubPrefix))
    rest = name.drop_front(4);
  else
    return std::nullopt;

  uint64_t addr = 0;
  if (rest.getAsInteger(16, addr))
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

/// Look up a block-function by PC, accepting both the `sub_` and `blk_`
/// naming conventions produced by BlockLifter.
llvm::Function *lookupBlockFunction(llvm::Module &M, uint64_t pc) {
  char name[64];
  snprintf(name, sizeof(name), "sub_%llx", (unsigned long long)pc);
  if (auto *fn = M.getFunction(name); fn && !fn->isDeclaration())
    return fn;
  snprintf(name, sizeof(name), "blk_%llx", (unsigned long long)pc);
  if (auto *fn = M.getFunction(name); fn && !fn->isDeclaration())
    return fn;
  return nullptr;
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

        if (isDispatchIntrinsicName(callee->getName())) {
          const bool is_call = isDispatchCallName(callee->getName());
          edge.kind = is_call ? LiftEdgeKind::kIndirectCall
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
        // Discover targets from dispatch_call/dispatch_jump intrinsics.
        bool is_dispatch = isDispatchIntrinsicName(name);
        // Also discover targets from raw __remill_function_call and
        // __remill_jump intrinsics in late-lifted blocks — these
        // haven't been lowered to dispatch_call yet but still carry
        // constant PC targets that should be lifted.
        bool is_remill_call =
            name == "__remill_function_call" || name == "__remill_jump";
        if (!is_dispatch && !is_remill_call)
          continue;
        if (call->arg_size() < 2)
          continue;
        auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!pc_arg)
          continue;
        uint64_t target_pc = pc_arg->getZExtValue();
        if (target_pc == 0)
          continue;
        // Check if a block-function already exists for this target under
        // either the `sub_` or `blk_` naming convention.
        if (!lookupBlockFunction(M, target_pc))
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
        if (isDispatchIntrinsicName(name))
          ++count;
      }
    }
  }
  return count;
}

/// Resolve VMP PUSH+JMP RSP stack-code dispatch patterns.
///
/// When a dispatch_jump targets RSP-8 (after a PUSH) and the pushed
/// value is a constant, the constant's bytes encode a handler stub.
/// This function decodes those bytes by injecting them as synthetic
/// code at a generated PC, then rewrites the dispatch_jump target to
/// that PC so the normal lift+resolve flow can handle it.
bool resolveStackCodeDispatches(
    llvm::Module &M, BinaryMemoryMap *mem_map,
    const AddCodeCallback &add_code) {
  if (!mem_map || !add_code)
    return false;

  static uint64_t synth_counter = 0;
  constexpr uint64_t kSynthBase = 0xFFFF'0000'0000'0000ULL;

  bool changed = false;
  auto *i64_ty = llvm::Type::getInt64Ty(M.getContext());

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
        if (!isDispatchIntrinsicName(callee->getName()))
          continue;
        if (call->arg_size() < 2)
          continue;

        // Already constant? Skip — resolveConstantDispatches handles it.
        if (llvm::isa<llvm::ConstantInt>(call->getArgOperand(1)))
          continue;

        // Pattern: target = sub(RSP_load, 8) — the PUSH pattern.
        auto *target = call->getArgOperand(1);
        auto *sub = llvm::dyn_cast<llvm::BinaryOperator>(target);
        if (!sub || sub->getOpcode() != llvm::Instruction::Sub)
          continue;
        auto *offset = llvm::dyn_cast<llvm::ConstantInt>(sub->getOperand(1));
        if (!offset || offset->getZExtValue() != 8)
          continue;

        // Walk backward in this BB to find:
        //   store i64 <const>, ptr inttoptr(target)
        llvm::ConstantInt *code_val = nullptr;
        for (auto it = call->getReverseIterator(); it != BB.rend(); ++it) {
          auto *si = llvm::dyn_cast<llvm::StoreInst>(&*it);
          if (!si)
            continue;
          // Check if store destination is inttoptr(target)
          auto *i2p =
              llvm::dyn_cast<llvm::IntToPtrInst>(si->getPointerOperand());
          if (!i2p)
            continue;
          if (i2p->getOperand(0) == target) {
            code_val =
                llvm::dyn_cast<llvm::ConstantInt>(si->getValueOperand());
            break;
          }
        }

        if (!code_val)
          continue;

        // Extract the constant's bytes as handler code.
        uint64_t raw = code_val->getZExtValue();
        uint8_t bytes[8];
        std::memcpy(bytes, &raw, 8);

        // Assign a synthetic PC and inject the code.
        uint64_t synth_pc = kSynthBase + (synth_counter++ * 0x100);
        mem_map->addRegion(synth_pc, bytes, 8,
                           /*read_only=*/true, /*executable=*/true);
        add_code(synth_pc, bytes, 8);

        // Rewrite the dispatch_jump target.
        call->setArgOperand(1,
                            llvm::ConstantInt::get(i64_ty, synth_pc));
        changed = true;
      }
    }
  }
  return changed;
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
        if (!isDispatchIntrinsicName(name))
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

        // Find the corresponding block-function under either naming.
        auto *target_fn = lookupBlockFunction(M, target_pc);
        if (!target_fn)
          continue;

        to_replace.push_back({call, target_fn});
      }
    }
  }

  for (auto &[call, target_fn] : to_replace) {
    // The dispatch call pattern is:
    //   %r = call @dispatcher(state, pc, mem)
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

/// Function-pass that rewrites musttail @__remill_missing_block calls whose
/// constant PC target falls in a non-executable section to `ret ptr %memory`.
/// This must run inside IterativeBlockDiscovery's per-round FPM so that
/// non-executable targets are caught *before* collapse passes kill the body.
struct RewriteNonExecMissingBlockFPM
    : llvm::PassInfoMixin<RewriteNonExecMissingBlockFPM> {
  llvm::PreservedAnalyses run(llvm::Function &F,
                              llvm::FunctionAnalysisManager &AM) {
    auto &MAMProxy =
        AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
    auto *binary_memory =
        MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
    if (!binary_memory || !binary_memory->imageBase())
      return llvm::PreservedAnalyses::all();

    auto *missing_fn = F.getParent()->getFunction("__remill_missing_block");
    if (!missing_fn || missing_fn->use_empty())
      return llvm::PreservedAnalyses::all();

    if (F.arg_size() < 3 || !F.getArg(2)->getType()->isPointerTy())
      return llvm::PreservedAnalyses::all();

    llvm::Value *memory = F.getArg(2);
    const auto image_base = binary_memory->imageBase();
    const auto image_size = binary_memory->imageSize();

    llvm::SmallVector<llvm::CallInst *, 4> to_rewrite;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call || call->getCalledFunction() != missing_fn)
          continue;
        if (call->arg_size() < 2)
          continue;
        auto *pc_const =
            llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1));
        if (!pc_const)
          continue;
        uint64_t target_pc = pc_const->getZExtValue();
        if (target_pc == 0)
          continue;
        bool in_image = target_pc >= image_base &&
                        target_pc < (image_base + image_size);
        if (in_image && !binary_memory->isExecutable(target_pc, 1))
          to_rewrite.push_back(call);
      }
    }

    if (to_rewrite.empty())
      return llvm::PreservedAnalyses::all();

    for (auto *call : to_rewrite) {
      auto *BB = call->getParent();
      call->replaceAllUsesWith(memory);
      llvm::SmallVector<llvm::BasicBlock *, 2> succs;
      if (BB->getTerminator())
        for (auto *S : llvm::successors(BB))
          succs.push_back(S);
      while (&BB->back() != call)
        BB->back().eraseFromParent();
      call->eraseFromParent();
      for (auto *S : succs)
        S->removePredecessor(BB);
      llvm::IRBuilder<> Builder(BB);
      Builder.CreateRet(memory);
    }
    return llvm::PreservedAnalyses::none();
  }

  static bool isRequired() { return true; }
};

void runDiscoveryFPM(llvm::Module &M, llvm::ModuleAnalysisManager &MAM,
                     llvm::FunctionPassManager &&FPM) {
  auto &FAM =
      MAM.getResult<llvm::FunctionAnalysisManagerModuleProxy>(M).getManager();
  llvm::SmallVector<llvm::Function *, 32> worklist;
  for (auto &F : M) {
    if (!isDiscoveryFunction(F) && !F.hasFnAttribute("omill.output_root"))
      continue;
    worklist.push_back(&F);
  }

  for (auto *F : worklist) {
    if (!F || F->isDeclaration())
      continue;
    auto PA = FPM.run(*F, FAM);
    FAM.invalidate(*F, PA);
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
      // Lower ALL remill intrinsics (Phase1 + Phase3) so that:
      // 1. Memory read/write intrinsics become load/store (needed for
      //    ConstantMemoryFolding to fold XCHG handler table reads)
      // 2. JMP/CALL templates get inlined and __remill_jump becomes
      //    dispatch_jump (needed for dispatch resolution)
      FPM.addPass(LowerRemillIntrinsicsPass(
          LowerCategories::Phase1 | LowerCategories::Call |
          LowerCategories::Jump | LowerCategories::Return));
      FPM.addPass(FoldProgramCounterPass());
      FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
      FPM.addPass(CombinedFixedPointDevirtPass());
      FPM.addPass(llvm::InstCombinePass());
      FPM.addPass(llvm::GVNPass());
      FPM.addPass(llvm::ADCEPass());
      FPM.addPass(RewriteNonExecMissingBlockFPM());
      FPM.addPass(llvm::SimplifyCFGPass());
      runDiscoveryFPM(M, MAM, std::move(FPM));
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
      // Note: do NOT run FPM on newly-lifted blocks here — the State
      // constant propagation in Step 2.5 needs raw loads from State
      // GEPs to be present for replacement.  The optimization happens
      // inside cloneWithStateConstants (inline + GVN).
    }

    // Step 2.5: Worklist-based State constant propagation through
    // dispatch_call, dispatch_jump, and musttail edges.  The worklist
    // handles multi-hop propagation, pass-through, and on-demand lifting
    // of missing block declarations internally.
    {
      IPCPLiftCallback ipcp_lift;
      if (lift_block) {
        ipcp_lift = [&](uint64_t pc) -> bool {
          if (session) session->queueTarget(pc);
          bool lifted = lift_block(pc);
          if (lifted) {
            if (session) session->noteLiftedTarget(pc);
            ever_changed = true;
          }
          return lifted;
        };
      }
      if (propagateStateConstantsWorklist(
              M, M.getDataLayout(), &MAM, ipcp_lift))
        ever_changed = true;
    }

    // Step 2.75: Resolve PUSH+JMP RSP stack-code dispatch patterns.
    // When the PUSH operand is a constant (from IPCP + ConstantMemoryFolding),
    // decode the constant's bytes as handler code at a synthetic PC.
    {
      auto &mem_map = MAM.getResult<BinaryMemoryAnalysis>(M);
      auto add_code = MAM.getResult<BlockLiftAnalysis>(M).add_code;
      if (resolveStackCodeDispatches(M, &mem_map, add_code))
        ever_changed = true;
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
