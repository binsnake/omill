#include "omill/Passes/VMHandlerInliner.h"

#include <cstdlib>
#include <string>

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/ModuleUtils.h>

#include "omill/Analysis/VirtualCalleeRegistry.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {
namespace {

bool envBoolEnabled(const char *name) {
  const char *v = std::getenv(name);
  if (!v || !*v)
    return false;
  auto sv = llvm::StringRef(v).lower();
  return !(sv == "0" || sv == "false" || sv == "off" || sv == "no");
}

bool emitInlineDiagMarkers() {
  if (envBoolEnabled("OMILL_SKIP_INLINE_DIAG_MARKERS"))
    return false;
  const char *force = std::getenv("OMILL_INLINE_DIAG_MARKERS");
  if (!force || !*force)
    return true;
  auto sv = llvm::StringRef(force).lower();
  return !(sv == "0" || sv == "false" || sv == "off" || sv == "no");
}

void emitInlineDiagMarker(llvm::CallBase &call, llvm::Function &callee,
                          llvm::StringRef phase) {
  auto *caller = call.getFunction();
  if (!caller)
    return;

  auto &M = *caller->getParent();
  auto &Ctx = M.getContext();
  auto *i8_ptr_ty = llvm::PointerType::getUnqual(Ctx);

  std::string text;
  llvm::raw_string_ostream os(text);
  os << "omill.inline phase=" << phase << "; caller=" << caller->getName()
     << "; callee=" << callee.getName();
  if (callee.getName().starts_with("sub_"))
    os << "; callee_va=0x" << llvm::utohexstr(omill::extractEntryVA(callee.getName()));
  os.flush();

  auto *str_data = llvm::ConstantDataArray::getString(Ctx, text, true);
  auto *str_gv = new llvm::GlobalVariable(
      M, str_data->getType(), true, llvm::GlobalValue::PrivateLinkage, str_data,
      "__omill_inline_diag");
  str_gv->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
  str_gv->setAlignment(llvm::Align(1));
  str_gv->setSection(".omill.inline.diag");

  auto *sink = M.getGlobalVariable("__omill_inline_diag_sink");
  if (!sink) {
    sink = new llvm::GlobalVariable(
        M, i8_ptr_ty, false, llvm::GlobalValue::InternalLinkage,
        llvm::ConstantPointerNull::get(i8_ptr_ty), "__omill_inline_diag_sink");
    sink->setAlignment(llvm::Align(8));
    sink->setSection(".omill.inline.diag");
  }

  auto *zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(Ctx), 0);
  llvm::SmallVector<llvm::Constant *, 2> idxs{zero, zero};
  llvm::Constant *str_ptr = llvm::ConstantExpr::getInBoundsGetElementPtr(
      str_data->getType(), str_gv, idxs);
  if (str_ptr->getType() != i8_ptr_ty)
    str_ptr = llvm::ConstantExpr::getPointerCast(str_ptr, i8_ptr_ty);

  llvm::IRBuilder<> B(&call);
  auto *store = B.CreateStore(str_ptr, sink, /*isVolatile=*/true);
  store->setAlignment(llvm::Align(8));

  llvm::appendToUsed(M, {str_gv, sink});
}

/// Count instructions in a function (excluding debug/lifetime intrinsics).
unsigned countMeaningfulInstructions(llvm::Function &F) {
  unsigned count = 0;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (llvm::isa<llvm::DbgInfoIntrinsic>(&I))
        continue;
      if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(&I)) {
        if (II->isLifetimeStartOrEnd())
          continue;
      }
      ++count;
    }
  }
  return count;
}

/// Check if a function is a lifted function (has remill signature or is
/// named sub_*).
bool isLiftedFunction(const llvm::Function &F) {
  auto name = F.getName();
  return name.starts_with("sub_") || name.starts_with("__lifted_");
}

bool hasUnresolvedDispatch(const llvm::Function &F) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB || CB->arg_size() < 2)
        continue;

      auto *callee = CB->getCalledFunction();
      if (!callee)
        continue;

      auto name = callee->getName();
      if (name != "__omill_dispatch_call" && name != "__omill_dispatch_jump")
        continue;

      auto *target = CB->getArgOperand(1);
      if (llvm::isa<llvm::ConstantInt>(target))
        continue;

      if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target)) {
        if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
          continue;
      }

      return true;
    }
  }

  return false;
}

/// Collect all direct call targets from a function, counting callsites.
void collectCallTargets(
    llvm::Function &F,
    llvm::DenseMap<llvm::Function *, unsigned> &target_counts) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;

      auto *callee = CB->getCalledFunction();
      if (!callee || callee->isDeclaration())
        continue;

      // Skip intrinsics and known non-handler functions.
      if (callee->isIntrinsic())
        continue;
      auto name = callee->getName();
      if (name.starts_with("__remill_") || name.starts_with("__omill_"))
        continue;

      target_counts[callee]++;
    }
  }
}

/// Identify VM handler candidates: small functions called from multiple
/// sites within lifted functions.
llvm::SmallVector<llvm::Function *, 16> identifyHandlers(
    llvm::Module &M, const VirtualCalleeRegistry *virtual_callees,
    unsigned max_instrs, unsigned min_callsites) {
  bool has_tagged_handlers = false;
  for (auto &F : M) {
    if (!F.isDeclaration() && F.hasFnAttribute("omill.vm_handler")) {
      has_tagged_handlers = true;
      break;
    }
  }

  // Count callsites across all lifted functions.
  llvm::DenseMap<llvm::Function *, unsigned> global_callsite_counts;

  for (auto &F : M) {
    if (F.isDeclaration() || !isLiftedFunction(F))
      continue;
    collectCallTargets(F, global_callsite_counts);
  }

  // Also count from _native wrappers (post-ABI recovery).
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.getName().ends_with("_native"))
      continue;
    collectCallTargets(F, global_callsite_counts);
  }

  llvm::SmallVector<llvm::Function *, 16> handlers;
  for (auto &[func, count] : global_callsite_counts) {
    if (has_tagged_handlers && !func->hasFnAttribute("omill.vm_handler"))
      continue;
    if (!has_tagged_handlers && count < min_callsites)
      continue;
    if (has_tagged_handlers && func->use_empty())
      continue;

    // Skip if function is too large to be a handler, UNLESS it's
    // explicitly tagged by the trace emulator — those are known VM handlers
    // that must be inlined regardless of size.
    unsigned size = countMeaningfulInstructions(*func);
    if (size > max_instrs && !func->hasFnAttribute("omill.vm_handler"))
      continue;

    // Skip functions that are lifted (sub_*) — those are real functions,
    // not VM handlers — UNLESS they're explicitly tagged as vm_handler
    // by the trace emulator (in which case they ARE handler bodies to inline).
    if (isLiftedFunction(*func) &&
        !func->hasFnAttribute("omill.vm_handler"))
      continue;

    // The VM wrapper is a boundary function: handlers get inlined INTO it,
    // but it must NOT be inlined into its callers (e.g. DriverEntry).
    // Demerged clones and outlined virtual-call wrappers are also boundaries:
    // they represent recovered per-call/per-hash functions that must stay
    // callable for further optimization.
    if (func->hasFnAttribute("omill.vm_wrapper") ||
        func->getFnAttribute("omill.vm_demerged_clone").isValid() ||
        func->getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
        (virtual_callees && virtual_callees->lookup(func->getName()).has_value()))
      continue;

    // Keep unresolved handler tails as explicit boundaries. Inlining them
    // smears one remaining unknown dispatch into the public output root.
    if (hasUnresolvedDispatch(*func))
      continue;

    handlers.push_back(func);
  }

  return handlers;
}

}  // namespace

llvm::PreservedAnalyses VMHandlerInlinerPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &virtual_callees = MAM.getResult<VirtualCalleeRegistryAnalysis>(M);
  auto handlers = identifyHandlers(M, &virtual_callees, max_handler_instrs_,
                                   min_callsites_);

  if (handlers.empty())
    return llvm::PreservedAnalyses::all();

  // Mark all handler functions as alwaysinline.
  bool attrs_changed = false;
  for (auto *F : handlers) {
    if (!F->hasFnAttribute(llvm::Attribute::AlwaysInline)) {
      F->addFnAttr(llvm::Attribute::AlwaysInline);
      attrs_changed = true;
    }
    if (F->hasFnAttribute(llvm::Attribute::NoInline)) {
      F->removeFnAttr(llvm::Attribute::NoInline);
      attrs_changed = true;
    }
    if (F->hasFnAttribute(llvm::Attribute::OptimizeNone)) {
      F->removeFnAttr(llvm::Attribute::OptimizeNone);
      attrs_changed = true;
    }
  }

  // Inline the marked functions iteratively.
  // After inlining function A into B, B may now contain calls to other
  // handlers (from A's body).  Re-scanning after each round catches these
  // transitive callsites.  musttail calls are stripped before inlining
  // because LLVM may refuse to inline them; after inlining the callee's
  // code is directly in the caller, so the tail-call property is moot.
  llvm::DenseSet<llvm::Function *> handler_set(handlers.begin(),
                                                handlers.end());

  bool inlined = false;
  bool round_changed;
  constexpr unsigned kMaxInlineRounds = 16;
  unsigned inline_round = 0;
  do {
    round_changed = false;
    llvm::SmallVector<llvm::CallBase *, 32> inline_sites;

    for (auto &F : M) {
      if (F.isDeclaration())
        continue;

      for (auto it = llvm::inst_begin(F), end = llvm::inst_end(F);
           it != end; ++it) {
        auto *CB = llvm::dyn_cast<llvm::CallBase>(&*it);
        if (!CB)
          continue;

        auto *callee = CB->getCalledFunction();
        if (!callee || !handler_set.contains(callee))
          continue;
        // Skip self-recursive calls.  Cyclic handler chains (A → B → A)
        // produce recursive calls after one round of inlining.  Inlining
        // these would double the function size every round, causing OOM.
        if (callee == &F)
          continue;

        inline_sites.push_back(CB);
      }
    }

    for (auto *CB : inline_sites) {
      auto *callee = CB->getCalledFunction();
      if (!callee)
        continue;
      if (emitInlineDiagMarkers())
        emitInlineDiagMarker(*CB, *callee, "vm_handler_inline");

      // Strip musttail — LLVM cannot inline musttail calls, but after
      // inlining the callee body is directly in the caller so the
      // tail-call guarantee is no longer needed.
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(CB)) {
        if (CI->isMustTailCall())
          CI->setTailCallKind(llvm::CallInst::TCK_None);
      }

      auto *caller = CB->getFunction();
      llvm::InlineFunctionInfo IFI;
      auto result = llvm::InlineFunction(*CB, IFI);
      if (result.isSuccess()) {
        round_changed = true;
        inlined = true;
        caller->addFnAttr("omill.needs_cleanup");
      }
    }
    if (++inline_round >= kMaxInlineRounds)
      break;
  } while (round_changed);

  // Clean up: remove handler functions that are now dead.
  for (auto *F : handlers) {
    if (!F->use_empty())
      continue;

    // VM handlers tagged by the trace emulator are implementation details
    // that should always be cleaned up after inlining, regardless of
    // linkage. Non-tagged handlers respect the original linkage guard.
    if (F->hasFnAttribute("omill.vm_handler") || !F->hasExternalLinkage()) {
      F->eraseFromParent();
    }
  }

  return (inlined || attrs_changed) ? llvm::PreservedAnalyses::none()
                                    : llvm::PreservedAnalyses::all();
}

}  // namespace omill
