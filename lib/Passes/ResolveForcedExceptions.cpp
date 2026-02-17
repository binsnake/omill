#include "omill/Passes/ResolveForcedExceptions.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/IntrinsicTable.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

// State offsets for handler arg registers (Win64 ABI).
static constexpr unsigned kStateRCX = 2248;
static constexpr unsigned kStateRDX = 2264;
static constexpr unsigned kStateR8 = 2344;
static constexpr unsigned kStateR9 = 2360;

/// Store an i64 to State at a given byte offset.
static void storeStateI64(llvm::IRBuilder<> &Builder, llvm::Value *state,
                          unsigned offset, llvm::Value *val) {
  auto *i8_ty = llvm::Type::getInt8Ty(Builder.getContext());
  auto *ptr = Builder.CreateGEP(i8_ty, state, Builder.getInt32(offset));
  Builder.CreateStore(val, ptr);
}

}  // namespace

llvm::PreservedAnalyses ResolveForcedExceptionsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto &M = *F.getParent();

  auto *excinfo =
      MAMProxy.getCachedResult<ExceptionInfoAnalysis>(M);
  if (!excinfo || excinfo->empty())
    return llvm::PreservedAnalyses::all();

  // Look up the RUNTIME_FUNCTION for this function's entry VA.
  uint64_t func_va = extractEntryVA(F.getName());
  if (func_va == 0)
    return llvm::PreservedAnalyses::all();

  auto *rt_entry = excinfo->lookup(func_va);
  if (!rt_entry || rt_entry->handler_va == 0)
    return llvm::PreservedAnalyses::all();

  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(M);

  // Handler must be a lifted function.
  auto *handler_fn = lifted ? lifted->lookup(rt_entry->handler_va) : nullptr;
  if (!handler_fn)
    return llvm::PreservedAnalyses::all();

  IntrinsicTable table(M);

  // Collect all __remill_error calls in this function.
  struct Candidate {
    llvm::CallInst *CI;
    llvm::BasicBlock *BB;
    llvm::Value *error_pc;
  };
  llvm::SmallVector<Candidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      if (table.classifyCall(CI) != IntrinsicKind::kError)
        continue;

      candidates.push_back({CI, CI->getParent(), CI->getArgOperand(1)});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  llvm::DenseSet<llvm::BasicBlock *> terminated_blocks;
  for (auto &[CI, BB, error_pc] : candidates) {
    // After inserting ret for a previous candidate, all subsequent
    // instructions in the same block were erased (including this CI).
    // Skip to avoid use-after-free.
    if (terminated_blocks.count(BB))
      continue;

    llvm::IRBuilder<> Builder(CI);

    // Save old successors before we replace the terminator.
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *mem = CI->getArgOperand(2);

    // Store handler args into State (Win64 SEH ABI):
    //   RCX = 0 (EXCEPTION_RECORD* — not needed for CFF)
    //   RDX = 0 (EstablisherFrame — not needed for CFF)
    //   R8  = synthetic CONTEXT VA (Rip = exception address)
    //   R9  = synthetic DC VA (DISPATCHER_CONTEXT* — has HandlerData)
    storeStateI64(Builder, state, kStateRCX, Builder.getInt64(0));
    storeStateI64(Builder, state, kStateRDX, Builder.getInt64(0));
    storeStateI64(Builder, state, kStateR8,
                  Builder.getInt64(rt_entry->ctx_synthetic_va));
    storeStateI64(Builder, state, kStateR9,
                  Builder.getInt64(rt_entry->dc_synthetic_va));

    // Call the lifted handler directly.  The handler dispatches internally
    // (call resolver, jmp rax) so no epilog is needed — the handler's own
    // dispatch_jump IS the continuation.
    auto *handler_result = Builder.CreateCall(
        handler_fn,
        {state, Builder.getInt64(rt_entry->handler_va), mem});

    auto *new_term = Builder.CreateRet(handler_result);

    // Mark handler for inlining so it merges into the caller.
    // Also internalize it so GlobalDCE removes it after inlining —
    // stale copies would confuse InterProceduralConstProp.
    handler_fn->addFnAttr(llvm::Attribute::AlwaysInline);
    handler_fn->setLinkage(llvm::GlobalValue::InternalLinkage);

    // Replace uses of the original __remill_error call and erase it.
    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    // Erase all dead instructions after the new terminator.
    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Update PHI nodes: ret has no BB successors.
    for (auto *succ : old_succs)
      succ->removePredecessor(BB);

    terminated_blocks.insert(BB);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
