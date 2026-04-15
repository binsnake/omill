#include "omill/Passes/ResolveAndLowerControlFlow.h"

#include <llvm/Analysis/ScalarEvolution.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/PatternMatch.h>
#include <llvm/Support/KnownBits.h>
#include <llvm/Support/Format.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/RemillStateVariableSolver.h"
#include "omill/Analysis/VirtualModel/Types.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/BC/BlockLifterAnalysis.h"
#include "omill/Utils/LiftedNames.h"

#include "JumpTableUtils.h"

namespace omill {

namespace {

bool debugResolveControlFlow() {
  static const bool enabled =
      (std::getenv("OMILL_DEBUG_RESOLVE_CONTROL_FLOW") != nullptr);
  return enabled;
}

bool debugJumpTables() {
  static const bool enabled =
      (std::getenv("OMILL_DEBUG_JUMP_TABLES") != nullptr);
  return enabled;
}

void copyVirtualExitAttrs(const llvm::CallBase &from, llvm::CallBase &to) {
  static constexpr llvm::StringLiteral kVirtualExitAttrs[] = {
      "omill.virtual_exit_disposition",
      "omill.virtual_exit_continuation_pc",
      "omill.virtual_exit_continuation_vip",
      "omill.virtual_exit_native_target_pc",
      "omill.virtual_exit_partial",
      "omill.virtual_exit_full",
      "omill.virtual_exit_reenters_vm",
  };
  for (auto name : kVirtualExitAttrs) {
    auto attr = from.getFnAttr(name);
    if (!attr.isValid())
      continue;
    to.addFnAttr(llvm::Attribute::get(to.getContext(), name,
                                      attr.getValueAsString()));
  }
}

std::optional<VirtualExitDisposition> getVirtualExitDisposition(
    const llvm::CallBase &call) {
  auto attr = call.getFnAttr("omill.virtual_exit_disposition");
  if (!attr.isValid() || !attr.isStringAttribute())
    return std::nullopt;

  auto text = attr.getValueAsString();
  if (text == "unknown")
    return VirtualExitDisposition::kUnknown;
  if (text == "stay_in_vm")
    return VirtualExitDisposition::kStayInVm;
  if (text == "vm_exit_terminal")
    return VirtualExitDisposition::kVmExitTerminal;
  if (text == "vm_exit_native_call_reenter")
    return VirtualExitDisposition::kVmExitNativeCallReenter;
  if (text == "vm_exit_native_exec_unknown_return")
    return VirtualExitDisposition::kVmExitNativeExecUnknownReturn;
  if (text == "vm_enter")
    return VirtualExitDisposition::kVmEnter;
  if (text == "nested_vm_enter")
    return VirtualExitDisposition::kNestedVmEnter;
  return std::nullopt;
}

bool shouldLowerResolvedInternalTarget(const llvm::CallBase &call) {
  auto disposition = getVirtualExitDisposition(call);
  if (!disposition.has_value())
    return true;

  switch (*disposition) {
    case VirtualExitDisposition::kUnknown:
    case VirtualExitDisposition::kStayInVm:
      return true;
    case VirtualExitDisposition::kVmExitTerminal:
    case VirtualExitDisposition::kVmExitNativeCallReenter:
    case VirtualExitDisposition::kVmExitNativeExecUnknownReturn:
    case VirtualExitDisposition::kVmEnter:
    case VirtualExitDisposition::kNestedVmEnter:
      return false;
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Phase 1: ResolveTargets — resolve constant-PC dispatch calls/jumps
// ===----------------------------------------------------------------------===

bool isAlreadyResolved(llvm::Value *target) {
  if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target))
    if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
      return true;
  return false;
}

bool resolveDispatchTargets(llvm::Function &F,
                            const BinaryMemoryMap *map,
                            const LiftedFunctionMap *lifted) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  bool changed = false;

  // --- Resolve dispatch_call targets ---
  {
    llvm::SmallVector<llvm::CallInst *, 4> candidates;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || !isDispatchCallName(callee->getName()))
          continue;
        if (call->arg_size() < 3)
          continue;

        auto *target = call->getArgOperand(1);
        if (isAlreadyResolved(target))
          continue;

        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(target);
        if (!ci)
          continue;

        candidates.push_back(call);
      }
    }

    for (auto *call : candidates) {
      if (!shouldLowerResolvedInternalTarget(*call)) {
        if (debugResolveControlFlow())
          llvm::errs() << "[resolve-cf] skip-call-exit " << F.getName()
                       << " callee=" << call->getCalledFunction()->getName()
                       << "\n";
        continue;
      }

      auto *ci = llvm::cast<llvm::ConstantInt>(call->getArgOperand(1));
      uint64_t target_pc = ci->getZExtValue();

      // Priority 1: IAT import lookup.
      if (map && map->hasImports()) {
        if (auto *imp = map->lookupImport(target_pc)) {
          auto *fn_type =
              llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
          auto fn_callee = M.getOrInsertFunction(imp->function, fn_type);
          auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
          if (fn) {
            fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
            llvm::IRBuilder<> Builder(call);
            auto *fn_addr = Builder.CreatePtrToInt(fn, i64_ty,
                                                    imp->function + ".addr");
            call->setArgOperand(1, fn_addr);
            changed = true;
            continue;
          }
        }
      }

      // Priority 2: Direct call to lifted function.
      auto *target_fn = lifted ? lifted->lookup(target_pc) : nullptr;
      if (!target_fn)
        target_fn = findLiftedOrBlockFunctionByPC(M, target_pc);
      if (debugResolveControlFlow()) {
        llvm::errs() << "[resolve-cf] call-target "
                     << target_pc
                     << " fn=" << (target_fn ? target_fn->getName() : "<null>")
                     << " in=" << F.getName() << "\n";
      }
      if (target_fn) {
        llvm::IRBuilder<> Builder(call);
        auto *direct_call = Builder.CreateCall(
            target_fn, {call->getArgOperand(0), ci, call->getArgOperand(2)});
        copyVirtualExitAttrs(*call, *direct_call);
        call->replaceAllUsesWith(direct_call);
        call->eraseFromParent();
        changed = true;
      }
    }
  }

  // --- Resolve dispatch_jump targets ---
  {
    struct JumpCandidate {
      llvm::CallInst *call;
      llvm::ReturnInst *ret;
      uint64_t target_pc = 0;
      llvm::Function *target_fn = nullptr;
    };
    llvm::SmallVector<JumpCandidate, 4> candidates;

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || !isDispatchJumpName(callee->getName()))
          continue;
        if (call->arg_size() < 3)
          continue;

        auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
        if (!ret)
          continue;

        uint64_t target_pc = 0;
        llvm::Function *target_fn = nullptr;
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
          target_pc = ci->getZExtValue();
        } else if (auto *ptoi =
                       llvm::dyn_cast<llvm::PtrToIntOperator>(call->getArgOperand(1))) {
          target_fn = llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
          if (!target_fn)
            continue;
        } else {
          continue;
        }

        candidates.push_back({call, ret, target_pc, target_fn});
      }
    }

    for (auto &[call, ret, target_pc, target_fn] : candidates) {
      if (!shouldLowerResolvedInternalTarget(*call)) {
        if (debugResolveControlFlow())
          llvm::errs() << "[resolve-cf] skip-jump-exit " << F.getName()
                       << " callee=" << call->getCalledFunction()->getName()
                       << "\n";
        continue;
      }

      auto *BB = call->getParent();
      llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

      auto lowerDirectJumpToFunction = [&](llvm::Function *direct_target,
                                           llvm::CallInst *dispatch_call,
                                           llvm::ReturnInst *dispatch_ret) {
        llvm::IRBuilder<> Builder(dispatch_call);
        auto *state = dispatch_call->getArgOperand(0);
        auto *pc_val = dispatch_call->getArgOperand(1);
        auto *mem = dispatch_call->getArgOperand(2);

        auto *tail_call = Builder.CreateCall(direct_target, {state, pc_val, mem});
        copyVirtualExitAttrs(*dispatch_call, *tail_call);
        tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
        auto *new_ret = Builder.CreateRet(tail_call);

        dispatch_call->replaceAllUsesWith(
            llvm::PoisonValue::get(dispatch_call->getType()));
        dispatch_ret->eraseFromParent();
        dispatch_call->eraseFromParent();

        while (&BB->back() != new_ret) {
          auto &dead = BB->back();
          if (!dead.use_empty())
            dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
          dead.eraseFromParent();
        }

        llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
            successors(BB).begin(), successors(BB).end());
        for (auto *old_succ : old_succs)
          if (!new_succs.count(old_succ))
            old_succ->removePredecessor(BB);

        changed = true;
      };

      if (target_fn) {
        lowerDirectJumpToFunction(target_fn, call, ret);
        continue;
      }

      // Priority 1: Intra-function branch.
      if (auto *target_bb = findBlockForPC(F, target_pc)) {
        llvm::IRBuilder<> Builder(call);
        auto *br = Builder.CreateBr(target_bb);

        call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
        ret->eraseFromParent();
        call->eraseFromParent();

        while (&BB->back() != br) {
          auto &dead = BB->back();
          if (!dead.use_empty())
            dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
          dead.eraseFromParent();
        }

        llvm::SmallPtrSet<llvm::BasicBlock *, 4> new_succs(
            successors(BB).begin(), successors(BB).end());
        for (auto *old_succ : old_succs)
          if (!new_succs.count(old_succ))
            old_succ->removePredecessor(BB);

        changed = true;
        continue;
      }

      // Priority 2: Inter-function tail call.
        target_fn = lifted ? lifted->lookup(target_pc) : nullptr;
        if (!target_fn)
          target_fn = findLiftedOrBlockFunctionByPC(M, target_pc);
      if (target_fn) {
        lowerDirectJumpToFunction(target_fn, call, ret);
        continue;
      }
    }
  }

  return changed;
}

// ===----------------------------------------------------------------------===
// Phase 2: RecoverTables — pattern-match jump table loads
// ===----------------------------------------------------------------------===

struct JumpTableCandidate {
  llvm::CallInst *dispatch_call;
  llvm::ReturnInst *ret;
  llvm::BranchInst *branch;
  llvm::LoadInst *table_load;
  jt::LinearAddress addr;
  uint64_t image_base;
  uint64_t num_entries;
};

bool recoverJumpTables(llvm::Function &F,
                       const BinaryMemoryMap *map,
                       const LiftedFunctionMap *lifted,
                       BlockLiftCallback lift_block = {}) {
  if (!map || map->empty())
    return false;

  llvm::SmallVector<JumpTableCandidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isDispatchJumpName(callee->getName()))
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *target = call->getArgOperand(1);

      // Skip already-constant targets (handled by ResolveTargets phase).
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      // Unwrap RVA conversion if present.
      auto [image_base, load_val] = jt::unwrapRVAConversion(target, &F);
      llvm::Value *dynamic_rva_base = nullptr;
      if (image_base == 0)
        jt::trySplitDynamicRVAConversion(target, dynamic_rva_base, load_val);
      if (debugJumpTables()) {
        llvm::errs() << "[resolve-cf-jt] inspect " << F.getName()
                     << " bb=" << BB.getName()
                     << " image_base=0x" << llvm::format_hex(image_base, 10)
                     << " dynamic_base=" << (dynamic_rva_base ? "yes" : "no")
                     << " target=";
        target->print(llvm::errs());
        llvm::errs() << " load_val=";
        load_val->print(llvm::errs());
        llvm::Value *dbg_lhs = nullptr;
        llvm::Value *dbg_rhs = nullptr;
        if (llvm::PatternMatch::match(
                target, llvm::PatternMatch::m_Add(
                            llvm::PatternMatch::m_Value(dbg_lhs),
                            llvm::PatternMatch::m_Value(dbg_rhs)))) {
          llvm::errs() << " lhs=";
          dbg_lhs->print(llvm::errs());
          llvm::errs() << " rhs=";
          dbg_rhs->print(llvm::errs());
          llvm::errs() << " lhs_stripped=";
          jt::stripSimpleValueCasts(dbg_lhs)->print(llvm::errs());
          llvm::errs() << " rhs_stripped=";
          jt::stripSimpleValueCasts(dbg_rhs)->print(llvm::errs());
        }
        llvm::errs() << "\n";
      }

      auto *table_load = jt::extractUnderlyingLoad(load_val, &F);
      if (!table_load) {
        if (debugJumpTables())
          llvm::errs() << "[resolve-cf-jt] reject:no-table-load\n";
        continue;
      }


      // Decompose load pointer into base + idx * stride.
      auto addr_info =
          jt::decomposeTableAddress(table_load->getPointerOperand(), &F);
      if (!addr_info && dynamic_rva_base && map && map->imageBase() != 0) {
        addr_info = jt::decomposeTableAddressWithDynamicBase(
            table_load->getPointerOperand(), dynamic_rva_base,
            map->imageBase());
        if (addr_info && image_base == 0)
          image_base = map->imageBase();
      }
      if (!addr_info) {
        if (debugJumpTables())
          llvm::errs() << "[resolve-cf-jt] reject:no-addr-decompose\n";
        continue;
      }

      // Find bounds.
      auto bound = jt::computeIndexRange(addr_info->index, call->getParent());
      if (!bound || *bound == 0 || *bound > 1024) {
        if (debugJumpTables())
          llvm::errs() << "[resolve-cf-jt] reject:bad-bound\n";
        continue;
      }

      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      auto *branch =
          ret ? nullptr : llvm::dyn_cast<llvm::BranchInst>(call->getNextNode());
      if (!ret) {
        if (!branch || branch->isConditional() || branch->getNumSuccessors() != 1) {
          if (debugJumpTables())
            llvm::errs() << "[resolve-cf-jt] reject:no-ret-or-join\n";
          continue;
        }
      }

      if (debugJumpTables()) {
        llvm::errs() << "[resolve-cf-jt] candidate base=0x"
                     << llvm::format_hex(addr_info->base, 10)
                     << " stride=" << addr_info->stride
                     << " bound=" << *bound
                     << " image_base=0x" << llvm::format_hex(image_base, 10)
                     << "\n";
      }

      candidates.push_back({call, ret, branch, table_load, *addr_info,
                            image_base, *bound});
    }
  }

  if (candidates.empty())
    return false;

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.addr;

    auto raw_entries = jt::readTableEntries(*map, addr.base, addr.stride,
                                            cand.num_entries);
    if (!raw_entries) {
      if (debugJumpTables()) {
        llvm::errs() << "[resolve-cf-jt] reject:unreadable-table base=0x"
                     << llvm::format_hex(addr.base, 10)
                     << " stride=" << addr.stride
                     << " count=" << cand.num_entries << "\n";
      }
      continue;
    }

    jt::applyRVAConversion(*raw_entries, cand.image_base, addr.stride);
    unsigned trimmed_invalid = jt::trimTrailingInvalidEntries(*raw_entries, *map);
    if (raw_entries->empty())
      continue;

    if (lift_block) {
      for (uint64_t target_va : *raw_entries) {
        if ((lifted && lifted->lookup(target_va)) ||
            F.getParent()->getFunction(
                (llvm::Twine("blk_") + llvm::Twine::utohexstr(target_va)).str()) ||
            F.getParent()->getFunction(
                (llvm::Twine("sub_") + llvm::Twine::utohexstr(target_va)).str())) {
          continue;
        }
        if (!map->isExecutable(target_va, 1))
          continue;
        bool lifted_target = lift_block(target_va);
        if (debugJumpTables()) {
          llvm::errs() << "[resolve-cf-jt] late-block-lift target=0x"
                       << llvm::format_hex(target_va, 10)
                       << " ok=" << lifted_target << "\n";
        }
      }
    }

    if (debugJumpTables()) {
      llvm::errs() << "[resolve-cf-jt] read-table first=0x"
                   << llvm::format_hex((*raw_entries)[0], 10)
                   << " last=0x"
                   << llvm::format_hex((*raw_entries)[raw_entries->size() - 1], 10)
                   << " trimmed_tail=" << trimmed_invalid << "\n";
    }

    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.image_base, cand.dispatch_call,
        cand.ret, cand.branch, F, *map, lifted);

    if (result.changed) {
      if (debugJumpTables())
        llvm::errs() << "[resolve-cf-jt] changed " << F.getName() << "\n";
      changed = true;
    } else if (debugJumpTables()) {
      llvm::errs() << "[resolve-cf-jt] build-switch-nochange " << F.getName()
                   << "\n";
    }
  }

  return changed;
}

// ===----------------------------------------------------------------------===
// Phase 3: SymbolicSolve — SCEV/KnownBits fallback for table index bounds
// ===----------------------------------------------------------------------===

std::optional<uint64_t> scevBound(llvm::ScalarEvolution &SE,
                                   llvm::Value *idx) {
  if (!SE.isSCEVable(idx->getType()))
    return std::nullopt;

  auto *scev = SE.getSCEV(idx);
  auto range = SE.getUnsignedRange(scev);
  if (range.isFullSet() || range.isEmptySet())
    return std::nullopt;

  auto upper = range.getUnsignedMax().getZExtValue();
  if (upper == 0 || upper > 1024)
    return std::nullopt;

  return upper + 1;  // exclusive
}

std::optional<uint64_t> knownBitsBound(const llvm::DataLayout &DL,
                                        llvm::Value *idx) {
  llvm::KnownBits KB = llvm::computeKnownBits(idx, DL);
  llvm::APInt max_val = ~KB.Zero;
  uint64_t upper = max_val.getZExtValue();
  if (upper == 0 || upper > 1024)
    return std::nullopt;
  return upper + 1;  // exclusive
}

struct TableAccess {
  llvm::LoadInst *load;
  jt::LinearAddress addr;
  uint64_t image_base;
};

std::optional<TableAccess> analyzeTarget(llvm::Value *target,
                                         llvm::Function &F,
                                         const BinaryMemoryMap *map) {
  auto [image_base, load_val] = jt::unwrapRVAConversion(target, &F);
  llvm::Value *dynamic_rva_base = nullptr;
  if (image_base == 0)
    jt::trySplitDynamicRVAConversion(target, dynamic_rva_base, load_val);

  auto *table_load = jt::extractUnderlyingLoad(load_val, &F);
  if (!table_load)
    return std::nullopt;

  auto addr_info =
      jt::decomposeTableAddress(table_load->getPointerOperand(), &F);
  if (!addr_info && dynamic_rva_base && map && map->imageBase() != 0) {
    addr_info = jt::decomposeTableAddressWithDynamicBase(
        table_load->getPointerOperand(), dynamic_rva_base,
        map->imageBase());
    if (addr_info && image_base == 0)
      image_base = map->imageBase();
  }
  if (!addr_info)
    return std::nullopt;

  return TableAccess{table_load, *addr_info, image_base};
}

bool symbolicJumpTableSolve(llvm::Function &F,
                             llvm::FunctionAnalysisManager &AM,
                             const BinaryMemoryMap *map,
                             const LiftedFunctionMap *lifted) {
  if (!map || map->empty())
    return false;

  auto &DL = F.getParent()->getDataLayout();

  llvm::ScalarEvolution *SE = nullptr;
  auto getSE = [&]() -> llvm::ScalarEvolution & {
    if (!SE)
      SE = &AM.getResult<llvm::ScalarEvolutionAnalysis>(F);
    return *SE;
  };

  struct Candidate {
    llvm::CallInst *dispatch_call;
    llvm::ReturnInst *ret;
    llvm::BranchInst *branch;
    TableAccess access;
    uint64_t num_entries;
  };

  llvm::SmallVector<Candidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isDispatchJumpName(callee->getName()))
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *target = call->getArgOperand(1);
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      auto access = analyzeTarget(target, F, map);
      if (!access)
        continue;

      auto *idx = access->addr.index;

      // Try multiple bounding strategies.
      std::optional<uint64_t> bound;

      // 1. Pattern-based.
      bound = jt::computeIndexRange(idx, call->getParent());

      // 2. SCEV-based.
      if (!bound) {
        auto scev_result = scevBound(getSE(), idx);
        if (scev_result)
          bound = scev_result;
      }

      // 3. KnownBits-based.
      if (!bound) {
        auto kb_result = knownBitsBound(DL, idx);
        if (kb_result)
          bound = kb_result;
      }

      if (!bound || *bound == 0 || *bound > 1024)
        continue;

      auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
      auto *branch =
          ret ? nullptr : llvm::dyn_cast<llvm::BranchInst>(call->getNextNode());
      if (!ret) {
        if (!branch || branch->isConditional() || branch->getNumSuccessors() != 1)
          continue;
      }

      candidates.push_back({call, ret, branch, *access, *bound});
    }
  }

  if (candidates.empty())
    return false;

  bool changed = false;

  for (auto &cand : candidates) {
    auto &addr = cand.access.addr;

    auto raw_entries =
        jt::readTableEntries(*map, addr.base, addr.stride, cand.num_entries);
    if (!raw_entries)
      continue;

    jt::applyRVAConversion(*raw_entries, cand.access.image_base, addr.stride);

    auto result = jt::buildSwitchFromEntries(
        *raw_entries, addr.index, cand.access.image_base,
        cand.dispatch_call, cand.ret, cand.branch, F, *map, lifted);

    if (result.changed)
      changed = true;
  }

  return changed;
}

// ===----------------------------------------------------------------------===
// Phase 4: MultiValueSwitch — read omill.solved_target_pcs metadata and
// build switch instructions for dispatch sites with 2-256 known targets.
// ===----------------------------------------------------------------------===

static bool multiValueSwitchRewrite(llvm::Function &F,
                                    const BinaryMemoryMap *map,
                                    const LiftedFunctionMap *lifted) {
  struct Candidate {
    llvm::CallInst *call;
    llvm::SmallVector<uint64_t, 8> targets;
  };
  llvm::SmallVector<Candidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (!isDispatchJumpName(callee->getName()) &&
          !isDispatchCallName(callee->getName()))
        continue;
      if (llvm::isa<llvm::ConstantInt>(CI->getArgOperand(1)))
        continue;

      auto maybe_targets = readSolvedTargetSet(*CI);
      if (!maybe_targets || maybe_targets->size() < 2 ||
          maybe_targets->size() > 256)
        continue;

      candidates.push_back({CI, std::move(*maybe_targets)});
    }
  }

  if (candidates.empty())
    return false;

  bool changed = false;
  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  for (auto &cand : candidates) {
    auto *CI = cand.call;
    auto *target_val = CI->getArgOperand(1);
    auto *BB = CI->getParent();

    auto *tail = BB->splitBasicBlock(CI->getIterator(), "mvsw.default");
    BB->getTerminator()->eraseFromParent();

    auto *sw = llvm::SwitchInst::Create(target_val, tail,
                                         cand.targets.size(), BB);

    for (uint64_t target_pc : cand.targets) {
      auto *case_bb = llvm::BasicBlock::Create(
          Ctx, "mvsw." + llvm::Twine::utohexstr(target_pc), &F);
      llvm::IRBuilder<> Builder(case_bb);

      llvm::SmallVector<llvm::Value *, 4> args;
      for (unsigned i = 0; i < CI->arg_size(); ++i) {
        if (i == 1)
          args.push_back(llvm::ConstantInt::get(i64_ty, target_pc));
        else
          args.push_back(CI->getArgOperand(i));
      }
      auto *new_call = Builder.CreateCall(CI->getCalledFunction(), args);
      new_call->setTailCallKind(CI->getTailCallKind());
      Builder.CreateBr(tail);

      sw->addCase(llvm::cast<llvm::ConstantInt>(
                      llvm::ConstantInt::get(target_val->getType(), target_pc)),
                  case_bb);
    }

    if (!CI->use_empty()) {
      auto *phi = llvm::PHINode::Create(CI->getType(),
                                         cand.targets.size() + 1,
                                         "mvsw.result");
      phi->insertBefore(tail->begin());
      for (auto *pred : llvm::predecessors(tail)) {
        llvm::CallInst *pred_call = nullptr;
        for (auto &PI : *pred)
          if (auto *c = llvm::dyn_cast<llvm::CallInst>(&PI))
            pred_call = c;
        phi->addIncoming(pred_call ? (llvm::Value *)pred_call
                                   : llvm::UndefValue::get(CI->getType()),
                         pred);
      }
      CI->replaceAllUsesWith(phi);
    }
    changed = true;
  }

  return changed;
}

}  // namespace

// ===----------------------------------------------------------------------===
// Main pass entry point
// ===----------------------------------------------------------------------===

llvm::PreservedAnalyses ResolveAndLowerControlFlowPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (debugJumpTables())
    llvm::errs() << "[resolve-cf-jt] run " << F.getName() << "\n";
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());
  auto *block_lift_result =
      MAMProxy.getCachedResult<BlockLiftAnalysis>(*F.getParent());
  auto lift_block =
      block_lift_result ? block_lift_result->lift_block : BlockLiftCallback{};

  bool changed = false;

  // Phase 1: Resolve constant-PC targets.
  if (phases_ & ResolvePhases::ResolveTargets)
    changed |= resolveDispatchTargets(F, map, lifted);

  // Phase 2: Recover jump tables via pattern matching.
  if (phases_ & ResolvePhases::RecoverTables)
    changed |= recoverJumpTables(F, map, lifted, lift_block);

  // Phase 3: Symbolic fallback for table index bounds.
  if (phases_ & ResolvePhases::SymbolicSolve)
    changed |= symbolicJumpTableSolve(F, AM, map, lifted);

  // Phase 4: Build switch from solver multi-target metadata.
  if (phases_ & ResolvePhases::MultiValueSwitch)
    changed |= multiValueSwitchRewrite(F, map, lifted);

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
