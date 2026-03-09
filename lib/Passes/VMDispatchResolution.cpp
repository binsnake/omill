#include "omill/Passes/VMDispatchResolution.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/VMTraceMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {
static std::optional<uint64_t> extractVAFromName(llvm::StringRef name) {
  uint64_t va = extractEntryVA(name);
  if (va == 0)
    return std::nullopt;
  return va;
}

static std::optional<uint64_t> extractTraceHashAttr(const llvm::Function &F) {
  auto attr = F.getFnAttribute("omill.vm_trace_in_hash");
  if (!attr.isValid() || !attr.isStringAttribute())
    return std::nullopt;

  uint64_t hash = 0;
  if (attr.getValueAsString().getAsInteger(16, hash))
    return std::nullopt;
  return hash;
}

static llvm::Function *findDemergedHandlerClone(llvm::Module &M,
                                                uint64_t handler_va,
                                                uint64_t incoming_hash) {
  if (auto *direct =
          M.getFunction(demergedHandlerCloneName(handler_va, incoming_hash)))
    return direct;

  for (auto &F : M) {
    if (extractVAFromName(F.getName()) != std::optional<uint64_t>(handler_va))
      continue;
    if (!F.getFnAttribute("omill.vm_demerged_clone").isValid())
      continue;
    auto hash = extractTraceHashAttr(F);
    if (hash && *hash == incoming_hash)
      return &F;
  }
  return nullptr;
}

static void collectDispatchJumps(
    llvm::Function &F, llvm::SmallVectorImpl<llvm::CallInst *> &dispatch_jumps) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || call->arg_size() < 3)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        dispatch_jumps.push_back(call);
    }
  }
}

}  // namespace

llvm::PreservedAnalyses VMDispatchResolutionPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &trace_map = MAM.getResult<VMTraceMapAnalysis>(M);
  if (trace_map.empty())
    return llvm::PreservedAnalyses::all();

  unsigned resolved_count = 0;
  unsigned skipped_count = 0;
  unsigned discovery_count = 0;
  llvm::DenseSet<uint64_t> discovered_targets;

  auto &ctx = M.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);

  for (auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.vm_handler"))
      continue;

    auto handler_va = extractVAFromName(F.getName());
    if (!handler_va)
      continue;

    auto exact_hash = extractTraceHashAttr(F);
    auto trace_targets = trace_map.getTraceTargets(*handler_va);
    llvm::Function *exact_clone_target = nullptr;

    // If this handler has no trace targets under its own VA, it may be a
    // thunk-resolved vmenter wrapper (remill folded the vmenter code into a
    // preceding thunk function).  Fall back to the first handler entry in the
    // trace map, which is the initial dispatch target of the VM.
    if (trace_targets.empty() && !exact_hash &&
        !trace_map.handlerEntries().empty() &&
        !trace_map.isVMHandler(*handler_va)) {
      trace_targets.push_back(trace_map.handlerEntries().front());
    }

    if (exact_hash) {
      if (auto exact_record = trace_map.getTraceForHash(*handler_va, *exact_hash)) {
        trace_targets = exact_record->successors;
        if (exact_record->successors.size() == 1 &&
            exact_record->outgoing_hash != 0) {
          exact_clone_target = findDemergedHandlerClone(
              M, exact_record->successors.front(), exact_record->outgoing_hash);
        }
      }
    }
    llvm::SmallVector<llvm::CallInst *, 4> dispatch_jumps;
    collectDispatchJumps(F, dispatch_jumps);

    // Check if this handler is a vmexit handler in the trace.
    bool is_vmexit_handler = false;
    if (exact_hash) {
      if (auto rec = trace_map.getTraceForHash(*handler_va, *exact_hash))
        is_vmexit_handler = rec->is_vmexit;
    } else {
      auto records = trace_map.getTraceRecords(*handler_va);
      for (auto &r : records) {
        if (r.is_vmexit) { is_vmexit_handler = true; break; }
      }
    }

    for (auto *call : dispatch_jumps) {
      if (llvm::isa<llvm::ConstantInt>(call->getArgOperand(1)))
        continue;

      // For vmexit handlers with no successors, the dispatch_jump is a
      // "return to caller".  Since the handler was inlined into the caller,
      // the continuation code is already right after the dispatch_jump.
      // Eliminate the call by replacing it with poison and letting DCE clean
      // it up later.
      if (trace_targets.empty() && is_vmexit_handler) {
        call->replaceAllUsesWith(
            llvm::PoisonValue::get(call->getType()));
        call->eraseFromParent();
        ++resolved_count;
        continue;
      }

      if (trace_targets.size() != 1) {
        ++skipped_count;
        continue;
      }

      uint64_t target_va = trace_targets.front();
      if (exact_clone_target) {
        llvm::IRBuilder<> builder(call);
        auto *fn_addr = builder.CreatePtrToInt(exact_clone_target, i64_ty,
                                               exact_clone_target->getName() + ".addr");
        call->setArgOperand(1, fn_addr);
      } else {
        call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, target_va));
      }
      ++resolved_count;

      if (!exact_clone_target) {
        std::string target_name =
            "sub_" + llvm::Twine::utohexstr(target_va).str();
        if (!M.getFunction(target_name))
          discovered_targets.insert(target_va);
      }
    }
  }

  if (!discovered_targets.empty()) {
    if (auto *old_md = M.getNamedMetadata("omill.vm_discovered_targets"))
      M.eraseNamedMetadata(old_md);

    auto *named_md = M.getOrInsertNamedMetadata("omill.vm_discovered_targets");
    for (auto va : discovered_targets) {
      auto *ci_md = llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(i64_ty, va));
      named_md->addOperand(llvm::MDTuple::get(ctx, {ci_md}));
    }
    discovery_count = discovered_targets.size();
  }

  llvm::errs() << "VMDispatchResolution: resolved " << resolved_count;
  if (skipped_count > 0)
    llvm::errs() << ", skipped " << skipped_count;
  if (discovery_count > 0)
    llvm::errs() << ", discovered " << discovery_count << " new targets";
  llvm::errs() << "\n";

  if (resolved_count == 0)
    return llvm::PreservedAnalyses::all();
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill