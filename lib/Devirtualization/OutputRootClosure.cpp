#include "omill/Devirtualization/OutputRootClosure.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include <algorithm>
#include <map>
#include <set>

#include "omill/Analysis/IterativeLiftingSession.h"
#include "omill/BC/BlockLifter.h"
#include "omill/Devirtualization/BoundaryFact.h"
#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

template <typename Fn>
void forEachFunctionInOutputRootClosure(const llvm::Module &M, Fn &&visit) {
  llvm::SmallVector<const llvm::Function *, 16> worklist;
  llvm::SmallPtrSet<const llvm::Function *, 32> visited;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.hasFnAttribute("omill.output_root") &&
        !F.hasFnAttribute("omill.closed_root_slice_root")) {
      continue;
    }
    worklist.push_back(&F);
  }

  while (!worklist.empty()) {
    auto *current = worklist.pop_back_val();
    if (!current || current->isDeclaration() || !visited.insert(current).second)
      continue;

    visit(*current);

    for (auto &BB : *current) {
      for (auto &I : BB) {
        if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
          if (auto *callee = CB->getCalledFunction();
              callee && !callee->isDeclaration()) {
            worklist.push_back(callee);
          }
        }
        for (llvm::Value *operand : I.operands()) {
          auto *maybe_callee = llvm::dyn_cast<llvm::Function>(operand);
          if (!maybe_callee || maybe_callee->isDeclaration())
            continue;
          worklist.push_back(maybe_callee);
        }
      }
    }
  }
}

std::vector<uint64_t> sortedValues(const llvm::DenseSet<uint64_t> &values) {
  std::vector<uint64_t> ordered(values.begin(), values.end());
  std::sort(ordered.begin(), ordered.end());
  return ordered;
}

VirtualExitDisposition getWorkItemExitDisposition(
    const OutputRootClosureWorkItem &item) {
  if (!item.boundary)
    return VirtualExitDisposition::kUnknown;
  return virtualExitDispositionFromBoundaryDisposition(
      item.boundary->exit_disposition);
}

std::optional<uint64_t> extractFunctionSitePc(const llvm::Function &F) {
  if (auto entry = extractEntryVA(F.getName()))
    return entry;
  if (auto block_pc = extractBlockPC(F.getName()))
    return block_pc;
  return std::nullopt;
}

std::string buildClosureWorkIdentity(const OutputRootClosureWorkItem &item) {
  std::string id = item.owner_function + ":" + std::to_string(item.site_index) +
                   ":" + std::to_string(static_cast<int>(item.source_kind)) +
                   ":";
  if (item.site_pc)
    id += llvm::utohexstr(*item.site_pc);
  id += ":" + llvm::utohexstr(item.target_pc);
  if (item.boundary && item.boundary->continuation_vip_pc) {
    id += ":" + llvm::utohexstr(*item.boundary->continuation_vip_pc);
  }
  if (item.boundary) {
    id += ":boundary:" + llvm::StringRef(toString(item.boundary->kind)).str();
    id += ":" +
          llvm::StringRef(toString(item.boundary->exit_disposition)).str();
    if (item.boundary->boundary_pc)
      id += ":pc:" + llvm::utohexstr(*item.boundary->boundary_pc);
    if (item.boundary->native_target_pc)
      id += ":native:" + llvm::utohexstr(*item.boundary->native_target_pc);
    if (item.boundary->is_partial_exit)
      id += ":partial";
    if (item.boundary->is_full_exit)
      id += ":full";
    if (item.boundary->reenters_vm)
      id += ":reenter";
    if (item.boundary->continuation_pc)
      id += ":cont:" + llvm::utohexstr(*item.boundary->continuation_pc);
    if (item.boundary->controlled_return_pc)
      id += ":cret:" + llvm::utohexstr(*item.boundary->controlled_return_pc);
    if (item.boundary->continuation_owner_id)
      id += ":owner:" + std::to_string(*item.boundary->continuation_owner_id);
    if (item.boundary->continuation_owner_kind !=
        VirtualStackOwnerKind::kUnknown) {
      id += ":ownerkind:" +
            std::to_string(
                static_cast<int>(item.boundary->continuation_owner_kind));
    }
    if (item.boundary->continuation_entry_transform) {
      id += ":xform:" + std::to_string(static_cast<int>(
                             item.boundary->continuation_entry_transform->kind));
      if (item.boundary->continuation_entry_transform->jump_target_pc) {
        id += ":xjmp:" + llvm::utohexstr(
                             *item.boundary->continuation_entry_transform
                                  ->jump_target_pc);
      }
    }
  }
  if (item.executable_target) {
    const auto &fact = *item.executable_target;
    id += ":fact:" + llvm::utohexstr(fact.raw_target_pc);
    id += ":" + llvm::StringRef(toString(fact.kind)).str();
    id += ":" + llvm::StringRef(toString(fact.trust)).str();
    if (fact.invalidated_executable_entry) {
      id += ":invalidated";
      if (fact.invalidated_entry_source_pc)
        id += ":" + llvm::utohexstr(*fact.invalidated_entry_source_pc);
      if (fact.invalidated_entry_failed_pc)
        id += ":" + llvm::utohexstr(*fact.invalidated_entry_failed_pc);
    }
    if (fact.effective_target_pc)
      id += ":effective:" + llvm::utohexstr(*fact.effective_target_pc);
    if (fact.canonical_owner_pc)
      id += ":owner:" + llvm::utohexstr(*fact.canonical_owner_pc);
    if (fact.exact_fallthrough_target)
      id += ":exact_fallthrough";
  }
  return id;
}

}  // namespace

OutputRootClosureTargetSummary collectOutputRootClosureTargets(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc,
    bool include_defined_targets) {
  llvm::DenseSet<uint64_t> constant_code_targets;
  llvm::DenseSet<uint64_t> constant_calli_targets;
  llvm::DenseSet<uint64_t> constant_dispatch_targets;
  llvm::DenseSet<uint64_t> annotated_vm_continuation_targets;

  forEachFunctionInOutputRootClosure(M, [&](const llvm::Function &F) {
    if (auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
        attr.isValid() && attr.isStringAttribute()) {
      llvm::SmallVector<llvm::StringRef, 8> parts;
      attr.getValueAsString().split(parts, ',', -1, /*KeepEmpty=*/false);
      for (auto part : parts) {
        uint64_t target = 0;
        if (part.empty() || part.getAsInteger(16, target))
          continue;
        target = normalize_target_pc(target);
        if (!is_code_address(target))
          continue;
        if (!include_defined_targets && has_defined_target(target))
          continue;
        annotated_vm_continuation_targets.insert(target);
      }
    }

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;

        if (auto *callee = call->getCalledFunction()) {
          if ((callee->getName() == "__remill_function_call" ||
               callee->getName() == "__remill_jump") &&
              call->arg_size() >= 3) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              uint64_t target = normalize_target_pc(ci->getZExtValue());
              if (!is_code_address(target))
                continue;
              if (!include_defined_targets && has_defined_target(target))
                continue;
              constant_code_targets.insert(target);
            }
          }

          if (call->arg_size() >= 2 &&
              callee->getName() != "__remill_jump" &&
              callee->getName() != "__remill_function_call" &&
              omill::isDispatchIntrinsicName(callee->getName())) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              uint64_t target = normalize_target_pc(ci->getZExtValue());
              if (!is_code_address(target))
                continue;
              if (!include_defined_targets && has_defined_target(target))
                continue;
              constant_dispatch_targets.insert(target);
            }
          }

          if (!callee->isDeclaration())
            continue;
          if (auto boundary_fact = readBoundaryFact(*callee);
              boundary_fact && boundary_fact->native_target_pc) {
            uint64_t target = normalize_target_pc(*boundary_fact->native_target_pc);
            if (is_code_address(target) &&
                (include_defined_targets || !has_defined_target(target))) {
              constant_code_targets.insert(target);
              continue;
            }
          }
          if (auto boundary_fact = readBoundaryFact(*callee);
              boundary_fact && boundary_fact->boundary_pc) {
            uint64_t target = normalize_target_pc(*boundary_fact->boundary_pc);
            if (is_code_address(target) &&
                (include_defined_targets || !has_defined_target(target))) {
              constant_code_targets.insert(target);
              continue;
            }
          }
          if (auto executable_fact = readExecutableTargetFact(*callee)) {
            uint64_t target = normalize_target_pc(executable_fact->raw_target_pc);
            if (is_code_address(target) &&
                (include_defined_targets || !has_defined_target(target))) {
              constant_code_targets.insert(target);
              continue;
            }
          }
          uint64_t target = omill::extractStructuralCodeTargetPC(*callee);
          if (target == 0 || !is_code_address(target))
            continue;
          if (!include_defined_targets && has_defined_target(target))
            continue;
          auto *FT = callee->getFunctionType();
          if (FT->getNumParams() != 3 ||
              FT->getReturnType() != llvm::PointerType::getUnqual(M.getContext()) ||
              FT->getParamType(0) != llvm::PointerType::getUnqual(M.getContext()) ||
              FT->getParamType(1) != llvm::Type::getInt64Ty(M.getContext()) ||
              FT->getParamType(2) != llvm::PointerType::getUnqual(M.getContext())) {
            continue;
          }
          constant_code_targets.insert(target);
          continue;
        }

        auto *callee_op = call->getCalledOperand()->stripPointerCasts();
        if (auto *callee_fn = llvm::dyn_cast<llvm::Function>(callee_op)) {
          if (callee_fn->getName().contains("CALLI") && call->arg_size() >= 3) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2))) {
              const uint64_t target = ci->getZExtValue();
              if (!is_code_address(target))
                continue;
              if (!include_defined_targets && has_defined_target(target))
                continue;
              constant_calli_targets.insert(target);
            }
          }
        }

        llvm::ConstantInt *ci = nullptr;
        if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(call->getCalledOperand())) {
          if (ce->getOpcode() == llvm::Instruction::IntToPtr)
            ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
        }
        if (!ci) {
          if (auto *itp =
                  llvm::dyn_cast<llvm::IntToPtrInst>(call->getCalledOperand())) {
            ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
          }
        }
        if (!ci)
          continue;
        const uint64_t target = ci->getZExtValue();
        if (!is_code_address(target))
          continue;
        if (!include_defined_targets && has_defined_target(target))
          continue;
        constant_code_targets.insert(target);
      }
    }
  });

  OutputRootClosureTargetSummary summary;
  summary.constant_code_targets = sortedValues(constant_code_targets);
  summary.constant_calli_targets = sortedValues(constant_calli_targets);
  summary.constant_dispatch_targets = sortedValues(constant_dispatch_targets);
  summary.annotated_vm_continuation_targets =
      sortedValues(annotated_vm_continuation_targets);
  return summary;
}

std::vector<OutputRootClosureWorkItem> collectOutputRootClosureWorkItems(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc,
    bool include_defined_targets) {
  std::vector<OutputRootClosureWorkItem> work_items;
  std::map<std::string, unsigned> next_site_index;
  std::set<std::string> seen_identities;

  auto add_item = [&](const llvm::Function &F, unsigned site_index,
                      uint64_t target_pc,
                      OutputRootClosureSourceKind source_kind,
                      const llvm::CallBase *call,
                      const llvm::Function *callee = nullptr,
                      bool vip_symbolic = false) {
    target_pc = normalize_target_pc(target_pc);
    if (!is_code_address(target_pc))
      return;
    OutputRootClosureWorkItem item;
    item.owner_function = F.getName().str();
    item.site_index = site_index;
    item.site_pc = extractFunctionSitePc(F);
    item.target_pc = target_pc;
    item.vip_symbolic = vip_symbolic;
    item.source_kind = source_kind;
    if (call) {
      item.boundary = readBoundaryFact(*call);
      if ((!item.boundary ||
           item.boundary->exit_disposition == BoundaryDisposition::kUnknown) &&
          callee) {
        if (auto callee_boundary = readBoundaryFact(*callee)) {
          if (!item.boundary) {
            item.boundary = callee_boundary;
          } else {
            *item.boundary =
                mergeBoundaryFacts(*item.boundary, *callee_boundary);
          }
        }
      }
      item.executable_target = readExecutableTargetFact(*call);
    }
    if (item.source_kind ==
            OutputRootClosureSourceKind::kMissingBlockHandlerTarget) {
      if (!item.boundary)
        item.boundary = BoundaryFact{};
      if (item.boundary->exit_disposition == BoundaryDisposition::kUnknown) {
        item.boundary->exit_disposition = BoundaryDisposition::kVmExitTerminal;
        item.boundary->kind = BoundaryKind::kTerminalBoundary;
        if (!item.boundary->boundary_pc)
          item.boundary->boundary_pc = target_pc;
      }
    }
    if (item.executable_target &&
        item.executable_target->invalidated_executable_entry &&
        item.source_kind ==
            OutputRootClosureSourceKind::kMissingBlockHandlerTarget) {
      item.source_kind = OutputRootClosureSourceKind::kInvalidatedExecutableTarget;
    }
    const auto item_disposition = getWorkItemExitDisposition(item);
    if (!include_defined_targets && has_defined_target(target_pc) &&
        item_disposition != VirtualExitDisposition::kVmEnter &&
        item_disposition != VirtualExitDisposition::kNestedVmEnter) {
      return;
    }
    item.identity = buildClosureWorkIdentity(item);
    if (!seen_identities.insert(item.identity).second)
      return;
    work_items.push_back(std::move(item));
  };

  forEachFunctionInOutputRootClosure(M, [&](const llvm::Function &F) {
    if (auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
        attr.isValid() && attr.isStringAttribute()) {
      llvm::SmallVector<llvm::StringRef, 8> parts;
      attr.getValueAsString().split(parts, ',', -1, /*KeepEmpty=*/false);
      for (auto part : parts) {
        uint64_t target = 0;
        if (part.empty() || part.getAsInteger(16, target))
          continue;
        add_item(F, next_site_index[F.getName().str()]++, target,
                 OutputRootClosureSourceKind::kAnnotatedVmContinuationTarget,
                 /*call=*/nullptr);
      }
    }

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        const unsigned site_index = next_site_index[F.getName().str()]++;

        if (auto *callee = call->getCalledFunction()) {
          if (callee->getName() == "__omill_missing_block_handler" &&
              call->arg_size() >= 1) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(0))) {
              add_item(F, site_index, ci->getZExtValue(),
                       OutputRootClosureSourceKind::kMissingBlockHandlerTarget,
                       call, callee);
            }
          }

          if ((callee->getName() == "__remill_function_call" ||
               callee->getName() == "__remill_jump") &&
              call->arg_size() >= 3) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              add_item(F, site_index, ci->getZExtValue(),
                       OutputRootClosureSourceKind::kConstantCodeTarget, call,
                       callee);
            }
          }

          if (call->arg_size() >= 2 &&
              omill::isDispatchIntrinsicName(callee->getName())) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
              add_item(
                  F, site_index, ci->getZExtValue(),
                  OutputRootClosureSourceKind::kConstantDispatchTarget, call,
                  callee,
                  /*vip_symbolic=*/
                  !llvm::isa<llvm::ConstantInt>(call->getArgOperand(1)));
            }
          }

          if (callee->isDeclaration()) {
            if (callee->getName().starts_with("__remill_") ||
                omill::isDispatchIntrinsicName(callee->getName())) {
              continue;
            }
            if (auto boundary_fact = readBoundaryFact(*callee);
                boundary_fact && boundary_fact->native_target_pc) {
              add_item(F, site_index, *boundary_fact->native_target_pc,
                       OutputRootClosureSourceKind::kConstantCodeTarget, call,
                       callee);
              continue;
            }
            if (auto boundary_fact = readBoundaryFact(*callee);
                boundary_fact && boundary_fact->boundary_pc) {
              add_item(F, site_index, *boundary_fact->boundary_pc,
                       OutputRootClosureSourceKind::kConstantCodeTarget, call,
                       callee);
              continue;
            }
            if (auto executable_fact = readExecutableTargetFact(*callee)) {
              add_item(F, site_index, executable_fact->raw_target_pc,
                       OutputRootClosureSourceKind::kConstantCodeTarget, call,
                       callee);
              continue;
            }
            uint64_t target = omill::extractStructuralCodeTargetPC(*callee);
            if (target != 0) {
              auto *FT = callee->getFunctionType();
              if (FT->getNumParams() == 3 &&
                  FT->getReturnType() ==
                      llvm::PointerType::getUnqual(M.getContext()) &&
                  FT->getParamType(0) ==
                      llvm::PointerType::getUnqual(M.getContext()) &&
                  FT->getParamType(1) == llvm::Type::getInt64Ty(M.getContext()) &&
                  FT->getParamType(2) ==
                      llvm::PointerType::getUnqual(M.getContext())) {
                add_item(F, site_index, target,
                         OutputRootClosureSourceKind::kConstantCodeTarget,
                         call, callee);
              }
            }
          }
        }

        auto *callee_op = call->getCalledOperand()->stripPointerCasts();
        if (auto *callee_fn = llvm::dyn_cast<llvm::Function>(callee_op)) {
          if (callee_fn->getName().contains("CALLI") && call->arg_size() >= 3) {
            if (auto *ci =
                    llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(2))) {
              add_item(F, site_index, ci->getZExtValue(),
                       OutputRootClosureSourceKind::kConstantCalliTarget, call,
                       callee_fn);
            }
          }
        }

        llvm::ConstantInt *ci = nullptr;
        if (auto *ce =
                llvm::dyn_cast<llvm::ConstantExpr>(call->getCalledOperand())) {
          if (ce->getOpcode() == llvm::Instruction::IntToPtr)
            ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
        }
        if (!ci) {
          if (auto *itp =
                  llvm::dyn_cast<llvm::IntToPtrInst>(call->getCalledOperand())) {
            ci = llvm::dyn_cast<llvm::ConstantInt>(itp->getOperand(0));
          }
        }
        if (ci) {
          add_item(F, site_index, ci->getZExtValue(),
                   OutputRootClosureSourceKind::kConstantCodeTarget, call);
        }
      }
    }
  });

  return work_items;
}

std::vector<uint64_t> collectVmUnresolvedContinuationTargets(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc) {
  llvm::DenseSet<uint64_t> continuation_targets;

  for (const auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
      continue;
    auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
    if (!attr.isValid() || !attr.isStringAttribute())
      continue;
    llvm::SmallVector<llvm::StringRef, 8> parts;
    attr.getValueAsString().split(parts, ',', -1, /*KeepEmpty=*/false);
    for (llvm::StringRef part : parts) {
      uint64_t target = 0;
      if (part.empty() || part.getAsInteger(16, target))
        continue;
      target = normalize_target_pc(target);
      if (!is_code_address(target) || has_defined_target(target))
        continue;
      continuation_targets.insert(target);
    }
  }

  return sortedValues(continuation_targets);
}

std::vector<OutputRootClosureWorkItem> collectVmUnresolvedContinuationWorkItems(
    const llvm::Module &M, llvm::function_ref<bool(uint64_t)> is_code_address,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<uint64_t(uint64_t)> normalize_target_pc) {
  std::vector<OutputRootClosureWorkItem> work_items;
  std::map<std::string, unsigned> next_site_index;
  std::set<std::string> seen_identities;

  for (const auto &F : M) {
    if (F.isDeclaration() || !F.hasFnAttribute("omill.output_root"))
      continue;
    auto attr = F.getFnAttribute("omill.vm_unresolved_continuation_targets");
    if (!attr.isValid() || !attr.isStringAttribute())
      continue;
    llvm::SmallVector<llvm::StringRef, 8> parts;
    attr.getValueAsString().split(parts, ',', -1, /*KeepEmpty=*/false);
    for (llvm::StringRef part : parts) {
      uint64_t target = 0;
      if (part.empty() || part.getAsInteger(16, target))
        continue;
      target = normalize_target_pc(target);
      if (!is_code_address(target) || has_defined_target(target))
        continue;
      OutputRootClosureWorkItem item;
      item.owner_function = F.getName().str();
      item.site_index = next_site_index[item.owner_function]++;
      item.site_pc = extractFunctionSitePc(F);
      item.target_pc = target;
      item.boundary = BoundaryFact{};
      item.boundary->exit_disposition = BoundaryDisposition::kStayInVm;
      item.boundary->kind = BoundaryKind::kContinuation;
      item.source_kind =
          OutputRootClosureSourceKind::kVmUnresolvedContinuationTarget;
      item.identity = buildClosureWorkIdentity(item);
      if (!seen_identities.insert(item.identity).second)
        continue;
      work_items.push_back(std::move(item));
    }
  }

  return work_items;
}

std::vector<uint64_t> collectLateLiftableOutputRootClosureTargets(
    const OutputRootClosureTargetSummary &summary,
    llvm::function_ref<bool(uint64_t)> has_defined_target,
    llvm::function_ref<bool(uint64_t)> is_executable_target,
    llvm::function_ref<bool(uint64_t)> should_skip_target) {
  llvm::DenseSet<uint64_t> closure_targets;
  for (uint64_t target : summary.constant_code_targets)
    closure_targets.insert(target);
  for (uint64_t target : summary.constant_calli_targets)
    closure_targets.insert(target);
  for (uint64_t target : summary.constant_dispatch_targets)
    closure_targets.insert(target);
  for (uint64_t target : summary.annotated_vm_continuation_targets)
    closure_targets.insert(target);

  std::vector<uint64_t> ordered = sortedValues(closure_targets);
  ordered.erase(std::remove_if(ordered.begin(), ordered.end(),
                               [&](uint64_t target) {
                                 return has_defined_target(target) ||
                                        !is_executable_target(target) ||
                                        should_skip_target(target);
                               }),
                ordered.end());
  return ordered;
}

unsigned lateLiftTargets(llvm::ArrayRef<uint64_t> targets,
                         BlockLifter &block_lifter,
                         IterativeLiftingSession &session,
                         llvm::function_ref<bool(uint64_t)> has_defined_target,
                         llvm::function_ref<bool(uint64_t)> is_executable_target,
                         llvm::function_ref<bool(uint64_t)> should_skip_target) {
  unsigned lifted_count = 0;
  llvm::SmallVector<uint64_t, 4> scratch_targets;
  for (uint64_t pc : targets) {
    if (has_defined_target(pc) || !is_executable_target(pc) ||
        should_skip_target(pc)) {
      continue;
    }
    scratch_targets.clear();
    if (auto *lifted_fn = block_lifter.LiftBlock(pc, scratch_targets)) {
      (void) lifted_fn;
      session.noteLiftedTarget(pc);
      ++lifted_count;
    }
  }
  return lifted_count;
}

}  // namespace omill
