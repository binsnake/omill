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
#include <llvm/Transforms/Utils/Cloning.h>

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

static std::optional<uint64_t> extractHexStringAttr(const llvm::Function &F,
                                                    llvm::StringRef name) {
  auto attr = F.getFnAttribute(name);
  if (!attr.isValid() || !attr.isStringAttribute())
    return std::nullopt;

  uint64_t value = 0;
  if (attr.getValueAsString().getAsInteger(16, value))
    return std::nullopt;
  return value;
}

static std::string specializedWrapperCloneName(uint64_t wrapper_va,
                                               uint64_t successor_va,
                                               uint64_t outgoing_hash) {
  return liftedFunctionName(wrapper_va) + "__vmwrap_" +
         llvm::Twine::utohexstr(successor_va).str() + "_" +
         llvm::Twine::utohexstr(outgoing_hash).str();
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

static llvm::Function *getOrCreateDemergedHandlerClone(llvm::Module &M,
                                                       uint64_t handler_va,
                                                       uint64_t incoming_hash) {
  if (auto *clone = findDemergedHandlerClone(M, handler_va, incoming_hash))
    return clone;

  auto *base_fn = M.getFunction(liftedFunctionName(handler_va));
  if (!base_fn || base_fn->isDeclaration())
    return nullptr;

  std::string clone_name =
      demergedHandlerCloneName(handler_va, incoming_hash);
  llvm::ValueToValueMapTy VMap;
  auto *clone = llvm::CloneFunction(base_fn, VMap);
  clone->setName(clone_name);
  clone->setLinkage(llvm::GlobalValue::InternalLinkage);
  clone->addFnAttr("omill.vm_handler");
  clone->addFnAttr("omill.vm_demerged_clone", "1");
  clone->addFnAttr("omill.vm_trace_in_hash",
                   llvm::Twine::utohexstr(incoming_hash).str());
  return clone;
}

static llvm::Function *getOrCreateSpecializedWrapperClone(llvm::Module &M,
                                                          uint64_t wrapper_va,
                                                          uint64_t successor_va,
                                                          uint64_t outgoing_hash) {
  auto clone_name =
      specializedWrapperCloneName(wrapper_va, successor_va, outgoing_hash);
  if (auto *clone = M.getFunction(clone_name))
    return clone;

  auto *base_fn = M.getFunction(liftedFunctionName(wrapper_va));
  if (!base_fn || base_fn->isDeclaration())
    return nullptr;

  llvm::ValueToValueMapTy VMap;
  auto *clone = llvm::CloneFunction(base_fn, VMap);
  clone->setName(clone_name);
  clone->setLinkage(llvm::GlobalValue::InternalLinkage);
  clone->addFnAttr("omill.vm_wrapper");
  clone->addFnAttr("omill.vm_handler");
  clone->addFnAttr("omill.vm_wrapper_specialized", "1");
  clone->addFnAttr("omill.vm_trace_successor",
                   llvm::Twine::utohexstr(successor_va).str());
  clone->addFnAttr("omill.vm_trace_out_hash",
                   llvm::Twine::utohexstr(outgoing_hash).str());
  return clone;
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
      if (isDispatchJumpName(callee->getName()))
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

  llvm::SmallVector<llvm::Function *, 32> worklist;
  llvm::DenseSet<llvm::Function *> queued_handlers;

  auto enqueue_handler = [&](llvm::Function *Fn) {
    if (!Fn || Fn->isDeclaration() || !Fn->hasFnAttribute("omill.vm_handler"))
      return;
    if (queued_handlers.insert(Fn).second)
      worklist.push_back(Fn);
  };

  for (auto &F : M)
    enqueue_handler(&F);

  while (!worklist.empty()) {
    llvm::Function &F = *worklist.pop_back_val();
    if (F.isDeclaration() || !F.hasFnAttribute("omill.vm_handler"))
      continue;

    auto handler_va = extractVAFromName(F.getName());
    if (!handler_va)
      continue;

    auto exact_hash = extractTraceHashAttr(F);
    auto forced_successor =
        extractHexStringAttr(F, "omill.vm_trace_successor");
    auto forced_out_hash =
        extractHexStringAttr(F, "omill.vm_trace_out_hash");
    auto trace_targets = trace_map.getTraceTargets(*handler_va);
    llvm::Function *exact_clone_target = nullptr;

    // If this handler has no trace targets under its own VA, it may be a
    // thunk-resolved vmenter wrapper (remill folded the vmenter code into a
    // preceding thunk function).  Fall back to the first handler entry in the
    // trace map, which is the initial dispatch target of the VM.
    uint64_t entry_handler_va = trace_map.entryHandlerVA();
    if (entry_handler_va == 0 && !trace_map.handlerEntries().empty())
      entry_handler_va = trace_map.handlerEntries().front();

    if (trace_targets.empty() && entry_handler_va != 0 &&
        !trace_map.isVMHandler(*handler_va)) {
      trace_targets.push_back(entry_handler_va);
      if (exact_hash) {
        exact_clone_target = getOrCreateDemergedHandlerClone(
            M, entry_handler_va, *exact_hash);
        enqueue_handler(exact_clone_target);
      }
    }

    // Resolve native call target if present (inner VM call boundary).
    uint64_t native_call_va = 0;
    if (exact_hash) {
      if (auto exact_record = trace_map.getTraceForHash(*handler_va, *exact_hash)) {
        trace_targets = exact_record->successors;
        native_call_va = exact_record->native_target_va;
        if (exact_record->successors.size() == 1 &&
            exact_record->outgoing_hash != 0) {
          exact_clone_target = getOrCreateDemergedHandlerClone(
              M, exact_record->successors.front(), exact_record->outgoing_hash);
          enqueue_handler(exact_clone_target);
        }
      }
    } else {
      auto records = trace_map.getTraceRecords(*handler_va);
      if (records.size() == 1) {
        const auto &record = records.front();
        trace_targets = record.successors;
        native_call_va = record.native_target_va;
        if (record.successors.size() == 1 && record.outgoing_hash != 0) {
          exact_clone_target = getOrCreateDemergedHandlerClone(
              M, record.successors.front(), record.outgoing_hash);
          enqueue_handler(exact_clone_target);
        }
      }
    }

    if (forced_successor && forced_out_hash) {
      trace_targets.clear();
      trace_targets.push_back(*forced_successor);
      exact_clone_target = getOrCreateDemergedHandlerClone(
          M, *forced_successor, *forced_out_hash);
      enqueue_handler(exact_clone_target);
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
        bool resolved_from_pc_eval = false;
        if (exact_hash || forced_out_hash) {
          auto pcs = collectPossiblePCValues(call->getArgOperand(1), F, 4);
          if (pcs.size() == 1 && pcs.front() != 0) {
            uint64_t target_va = pcs.front();
            call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, target_va));
            ++resolved_count;
            discovered_targets.insert(target_va);
            resolved_from_pc_eval = true;
          }
        }
        if (!resolved_from_pc_eval) {
          ++skipped_count;
          continue;
        }
      }

      uint64_t target_va = 0;
      if (trace_targets.size() == 1) {
        target_va = trace_targets.front();
        if (exact_clone_target) {
          llvm::IRBuilder<> builder(call);
          auto *fn_addr = builder.CreatePtrToInt(exact_clone_target, i64_ty,
                                                 exact_clone_target->getName() + ".addr");
          call->setArgOperand(1, fn_addr);
        } else {
          call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, target_va));
        }
        ++resolved_count;
      }

      // Emit native call before the dispatch_jump if this handler has a
      // native call target (e.g. vmenter wrapper for inner VM re-entry).
      // The call uses the same (state, pc, mem) convention as lifted
      // functions.  After inlining + ABI recovery, this becomes a proper
      // function call in the output IR.
      if (native_call_va != 0) {
        std::string native_fn_name =
            "sub_" + llvm::Twine::utohexstr(native_call_va).str();
        llvm::Function *native_fn = M.getFunction(native_fn_name);
        if (native_fn && native_fn->hasFnAttribute("omill.vm_wrapper") &&
            trace_targets.size() == 1) {
          uint64_t specialized_successor = trace_targets.front();
          uint64_t specialized_out_hash = 0;
          if (forced_out_hash) {
            specialized_out_hash = *forced_out_hash;
          } else if (exact_hash) {
            if (auto exact_record =
                    trace_map.getTraceForHash(*handler_va, *exact_hash)) {
              specialized_out_hash = exact_record->outgoing_hash;
            }
          } else {
            auto records = trace_map.getTraceRecords(*handler_va);
            if (records.size() == 1)
              specialized_out_hash = records.front().outgoing_hash;
          }

          if (specialized_out_hash != 0) {
            if (auto *specialized = getOrCreateSpecializedWrapperClone(
                    M, native_call_va, specialized_successor,
                    specialized_out_hash)) {
              native_fn = specialized;
              enqueue_handler(specialized);
            }
          }
        }

        if (native_fn) {
          llvm::IRBuilder<> builder(call);
          auto *state = call->getArgOperand(0);
          auto *mem = call->getArgOperand(2);
          auto *pc = llvm::ConstantInt::get(i64_ty, native_call_va);
          builder.CreateCall(native_fn, {state, pc, mem});
        } else {
          // Function not yet lifted — schedule for discovery.
          discovered_targets.insert(native_call_va);
        }
      }

      if (!exact_clone_target && target_va != 0) {
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
