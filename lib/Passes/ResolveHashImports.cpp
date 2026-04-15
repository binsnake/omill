#include "omill/Passes/ResolveHashImports.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/IR/ValueHandle.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>

#include "omill/Utils/ImportHashDB.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

// ============================================================================
// Annotation helpers (from HashImportAnnotation)
// ============================================================================

static bool containsFNVMultiply(llvm::Loop *L) {
  for (auto *BB : L->blocks()) {
    for (auto &I : *BB) {
      auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!bin || bin->getOpcode() != llvm::Instruction::Mul)
        continue;
      for (auto &op : bin->operands()) {
        if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(op.get())) {
          if (ci->getZExtValue() == 16777619u)
            return true;
        }
      }
    }
  }
  return false;
}

static void collectSeeds(llvm::Loop *L,
                         llvm::SmallVectorImpl<uint32_t> &seeds) {
  for (auto &phi : L->getHeader()->phis()) {
    for (unsigned k = 0; k < phi.getNumIncomingValues(); ++k) {
      if (L->contains(phi.getIncomingBlock(k)))
        continue;
      auto *ci = llvm::dyn_cast<llvm::ConstantInt>(phi.getIncomingValue(k));
      if (!ci)
        continue;
      uint32_t seed = static_cast<uint32_t>(ci->getZExtValue());
      if (seed >= 0x100)
        seeds.push_back(seed);
    }
  }
  for (auto *sub : L->getSubLoops())
    collectSeeds(sub, seeds);
}

static const ImportHashDB &getSharedDB() {
  static const ImportHashDB db = [] {
    ImportHashDB d;
    d.loadBuiltins();
    d.buildLookupTables();
    return d;
  }();
  return db;
}

// ============================================================================
// Resolution helpers (from ResolveLazyImports)
// ============================================================================

static constexpr unsigned kRAXOffset = 2216;

static llvm::Loop *getOutermostLoop(llvm::Loop *L) {
  while (L->getParentLoop())
    L = L->getParentLoop();
  return L;
}

static llvm::CallInst *findDispatchCall(llvm::BasicBlock *BB) {
  for (auto &I : *BB) {
    if (auto *call = llvm::dyn_cast<llvm::CallInst>(&I)) {
      auto *callee = call->getCalledFunction();
      if (callee && isDispatchCallName(callee->getName()))
        return call;
    }
  }
  return nullptr;
}

static llvm::CallInst *findAnyCall(llvm::BasicBlock *BB, bool want_indirect) {
  for (auto &I : *BB) {
    auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
    if (!call)
      continue;
    if (want_indirect && call->getCalledFunction())
      continue;
    return call;
  }
  return nullptr;
}

static bool isStoreToStateOffset(llvm::StoreInst *store,
                                 llvm::Value *state_ptr, unsigned offset) {
  auto *gep = llvm::dyn_cast<llvm::GEPOperator>(store->getPointerOperand());
  if (!gep || gep->getPointerOperand() != state_ptr)
    return false;
  if (gep->getNumIndices() != 1)
    return false;
  auto *idx = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(1));
  return idx && idx->getZExtValue() == offset;
}

static llvm::Value *buildResolvedImportReturn(llvm::IRBuilder<> &Builder,
                                              llvm::Function &F,
                                              llvm::Function *resolved_fn,
                                              llvm::StringRef func_name) {
  llvm::Type *ret_ty = F.getReturnType();
  if (ret_ty->isVoidTy())
    return nullptr;
  if (ret_ty->isIntegerTy())
    return Builder.CreatePtrToInt(resolved_fn, ret_ty,
                                  func_name.str() + ".addr");
  if (ret_ty->isPointerTy())
    return Builder.CreatePointerCast(resolved_fn, ret_ty,
                                      func_name.str() + ".ptr");
  return nullptr;
}

/// A resolved hash import candidate ready for lowering.
struct ResolvedCandidate {
  llvm::ICmpInst *icmp;
  std::string module_name;
  std::string func_name;
};

// ============================================================================
// Annotation phase: detect FNV hash patterns, resolve via ImportHashDB
// ============================================================================

static bool annotateHashImports(
    llvm::Function &F, llvm::LoopInfo &LI,
    llvm::SmallVectorImpl<ResolvedCandidate> &resolved) {
  const auto &db = getSharedDB();
  auto &Ctx = F.getContext();
  bool changed = false;

  auto extractHashConstant =
      [](llvm::ICmpInst *icmp) -> std::optional<uint32_t> {
    for (unsigned i = 0; i < 2; ++i) {
      auto *CI = llvm::dyn_cast<llvm::ConstantInt>(icmp->getOperand(i));
      if (!CI)
        continue;
      uint64_t val = CI->getZExtValue();
      if (CI->getBitWidth() <= 32) {
        uint32_t h = static_cast<uint32_t>(val);
        if (h >= 0x100)
          return h;
        continue;
      }
      uint32_t upper = static_cast<uint32_t>(val >> 32);
      if (upper == 0 || upper == 0xFFFFFFFF) {
        uint32_t h = static_cast<uint32_t>(val);
        if (h >= 0x100)
          return h;
      }
    }
    return std::nullopt;
  };

  struct HashCandidate {
    llvm::ICmpInst *icmp;
    uint32_t hash_value;
  };

  llvm::SmallVector<HashCandidate, 8> all_candidates;
  llvm::SmallVector<HashCandidate, 8> unresolved_candidates;

  for (auto &BB : F) {
    auto *L = LI.getLoopFor(&BB);
    if (!L)
      continue;

    for (auto &I : BB) {
      auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(&I);
      if (!icmp || icmp->getPredicate() != llvm::ICmpInst::ICMP_EQ)
        continue;

      bool is_branch_cond = false;
      for (auto *user : icmp->users()) {
        if (auto *br = llvm::dyn_cast<llvm::BranchInst>(user)) {
          if (br->isConditional()) {
            is_branch_cond = true;
            break;
          }
        }
      }
      if (!is_branch_cond)
        continue;

      auto hash_opt = extractHashConstant(icmp);
      if (!hash_opt)
        continue;
      uint32_t hash_value = *hash_opt;

      all_candidates.push_back({icmp, hash_value});

      // Strategy 1: Dynamic seed extraction.
      bool annotation_resolved = false;
      llvm::Loop *fnv_loop = nullptr;
      for (auto *loop = L; loop; loop = loop->getParentLoop()) {
        if (containsFNVMultiply(loop))
          fnv_loop = loop;
      }
      if (fnv_loop) {
        llvm::SmallVector<uint32_t, 8> seeds;
        collectSeeds(fnv_loop, seeds);
        for (uint32_t seed : seeds) {
          auto result = db.resolve(seed, hash_value);
          if (result) {
            auto *mod_str = llvm::MDString::get(Ctx, result->module);
            auto *fn_str = llvm::MDString::get(Ctx, result->function);
            auto *md = llvm::MDNode::get(Ctx, {mod_str, fn_str});
            icmp->setMetadata("omill.resolved_import", md);
            resolved.push_back({icmp, result->module, result->function});
            changed = true;
            annotation_resolved = true;
            break;
          }
        }
      }

      // Strategy 2: Precomputed lookup tables.
      if (!annotation_resolved) {
        auto result = db.tryResolve(hash_value);
        if (result) {
          auto *mod_str = llvm::MDString::get(Ctx, result->entry.module);
          auto *fn_str = llvm::MDString::get(Ctx, result->entry.function);
          auto *md = llvm::MDNode::get(Ctx, {mod_str, fn_str});
          icmp->setMetadata("omill.resolved_import", md);
          resolved.push_back(
              {icmp, result->entry.module, result->entry.function});
          changed = true;
          annotation_resolved = true;
        }
      }

      if (!annotation_resolved)
        unresolved_candidates.push_back({icmp, hash_value});
    }
  }

  // Strategy 3: Paired hash resolution for CW_IMPORT.
  if (!unresolved_candidates.empty()) {
    for (auto &cand : unresolved_candidates) {
      if (cand.icmp->getMetadata("omill.resolved_import"))
        continue;

      auto mod_name = db.resolveModuleName(cand.hash_value);
      if (!mod_name)
        continue;

      for (auto &other : all_candidates) {
        if (other.icmp == cand.icmp)
          continue;

        auto func_entry = db.resolveInModule(*mod_name, other.hash_value);
        if (!func_entry)
          continue;

        auto *mod_str = llvm::MDString::get(Ctx, func_entry->module);
        auto *fn_str = llvm::MDString::get(Ctx, func_entry->function);
        auto *md = llvm::MDNode::get(Ctx, {mod_str, fn_str});
        if (!other.icmp->getMetadata("omill.resolved_import")) {
          other.icmp->setMetadata("omill.resolved_import", md);
          resolved.push_back(
              {other.icmp, func_entry->module, func_entry->function});
          changed = true;
        }

        auto *mod_only_md = llvm::MDNode::get(
            Ctx, {mod_str, llvm::MDString::get(Ctx, "")});
        cand.icmp->setMetadata("omill.resolved_import", mod_only_md);
        changed = true;
        break;
      }
    }
  }

  return changed;
}

// ============================================================================
// Resolution phase: rewrite PEB-walking loops to direct imports
// ============================================================================

static bool resolveAnnotatedImports(
    llvm::Function &F,
    llvm::SmallVectorImpl<ResolvedCandidate> &resolved) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  llvm::Value *state_ptr =
      F.getArg(0)->getType()->isPointerTy() ? F.getArg(0) : nullptr;

  // Also pick up any pre-existing metadata from earlier passes (backward
  // compat with external tooling that attaches metadata manually).
  llvm::DenseSet<llvm::ICmpInst *> already_resolved;
  for (auto &cand : resolved)
    already_resolved.insert(cand.icmp);

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        if (already_resolved.contains(icmp))
          continue;
        auto *md = icmp->getMetadata("omill.resolved_import");
        if (!md || md->getNumOperands() < 2)
          continue;
        auto *fn_str = llvm::dyn_cast<llvm::MDString>(md->getOperand(1));
        if (!fn_str || fn_str->getString().empty())
          continue;
        auto *mod_str = llvm::dyn_cast<llvm::MDString>(md->getOperand(0));
        resolved.push_back(
            {icmp,
             mod_str ? mod_str->getString().str() : "",
             fn_str->getString().str()});
      }
    }
  }

  if (resolved.empty())
    return false;

  // Use WeakVH to track icmps that may be deleted during iteration.
  struct ResolvableEntry {
    llvm::WeakVH vh;
    llvm::StringRef func_name;
  };
  llvm::SmallVector<ResolvableEntry, 4> entries;
  for (auto &cand : resolved) {
    if (cand.func_name.empty())
      continue;
    entries.push_back({cand.icmp, cand.func_name});
  }

  bool changed = false;
  for (auto &entry : entries) {
    llvm::Value *v = entry.vh;
    if (!v)
      continue;
    auto *icmp = llvm::cast<llvm::ICmpInst>(v);
    llvm::StringRef func_name = entry.func_name;

    llvm::BasicBlock *icmp_bb = icmp->getParent();
    auto *br = llvm::dyn_cast<llvm::BranchInst>(icmp_bb->getTerminator());
    llvm::CallInst *dispatch = nullptr;
    bool is_native_indirect_dispatch = false;
    if (br && br->isConditional() && br->getCondition() == icmp) {
      dispatch = findDispatchCall(br->getSuccessor(0));
      if (!dispatch) {
        dispatch = findAnyCall(br->getSuccessor(0), /*want_indirect=*/true);
        is_native_indirect_dispatch = (dispatch != nullptr);
      }
    }

    llvm::FunctionType *fn_type = nullptr;
    if (dispatch && is_native_indirect_dispatch)
      fn_type = dispatch->getFunctionType();
    else
      fn_type = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);

    auto fn_callee = M.getOrInsertFunction(func_name, fn_type);
    auto *fn = M.getFunction(func_name);
    if (!fn)
      continue;
    fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);

    if (dispatch) {
      llvm::IRBuilder<> Builder(dispatch);
      if (is_native_indirect_dispatch) {
        dispatch->setCalledOperand(fn_callee.getCallee());
      } else {
        auto *fn_addr = Builder.CreatePtrToInt(fn, Builder.getInt64Ty(),
                                                func_name.str() + ".addr");
        dispatch->setArgOperand(1, fn_addr);
      }

      if (state_ptr) {
        Builder.SetInsertPoint(dispatch->getNextNode());
        auto *rax_gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                           Builder.getInt64(kRAXOffset),
                                           "rax.gep.post.call");
        auto *rax_result = Builder.CreateLoad(Builder.getInt64Ty(), rax_gep,
                                               "rax.after.call");

        llvm::BasicBlock *dispatch_bb = dispatch->getParent();
        bool past_load = false;
        for (auto &I : *dispatch_bb) {
          if (&I == rax_result) {
            past_load = true;
            continue;
          }
          if (!past_load)
            continue;
          if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
            if (isStoreToStateOffset(store, state_ptr, kRAXOffset))
              store->setOperand(0, rax_result);
          }
        }
      }

      icmp->replaceAllUsesWith(llvm::ConstantInt::getTrue(Ctx));
      icmp->eraseFromParent();
      changed = true;
    } else {
      llvm::DominatorTree DT(F);
      llvm::LoopInfo LI(DT);

      llvm::Loop *inner_loop = LI.getLoopFor(icmp_bb);
      if (!inner_loop) {
        icmp->replaceAllUsesWith(llvm::ConstantInt::getTrue(Ctx));
        icmp->eraseFromParent();
        changed = true;
        continue;
      }

      llvm::Loop *outer_loop = getOutermostLoop(inner_loop);
      llvm::BasicBlock *preheader = outer_loop->getLoopPreheader();
      if (!preheader) {
        icmp->replaceAllUsesWith(llvm::ConstantInt::getTrue(Ctx));
        icmp->eraseFromParent();
        changed = true;
        continue;
      }

      auto *shortcut = llvm::BasicBlock::Create(Ctx, "resolved", &F);
      {
        llvm::IRBuilder<> Builder(shortcut);
        if (state_ptr) {
          auto *rax_gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                             Builder.getInt64(kRAXOffset));
          auto *fn_addr = Builder.CreatePtrToInt(fn, Builder.getInt64Ty(),
                                                  func_name.str() + ".addr");
          Builder.CreateStore(fn_addr, rax_gep);
          Builder.CreateRet(llvm::PoisonValue::get(F.getReturnType()));
        } else {
          llvm::Value *retv =
              buildResolvedImportReturn(Builder, F, fn, func_name);
          if (!retv && !F.getReturnType()->isVoidTy()) {
            shortcut->eraseFromParent();
            continue;
          }
          if (F.getReturnType()->isVoidTy())
            Builder.CreateRetVoid();
          else
            Builder.CreateRet(retv);
        }
      }

      preheader->getTerminator()->eraseFromParent();
      llvm::BranchInst::Create(shortcut, preheader);
      llvm::EliminateUnreachableBlocks(F);
      changed = true;
    }
  }

  return changed;
}

}  // namespace

// ============================================================================
// Pass entry point
// ============================================================================

llvm::PreservedAnalyses ResolveHashImportsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();
  if (F.arg_size() == 0)
    return llvm::PreservedAnalyses::all();

  auto &LI = AM.getResult<llvm::LoopAnalysis>(F);

  // Phase 1: Annotate hash comparisons with resolved import metadata.
  llvm::SmallVector<ResolvedCandidate, 4> resolved;
  bool changed = annotateHashImports(F, LI, resolved);

  // Phase 2: Lower annotated imports to direct references.
  changed |= resolveAnnotatedImports(F, resolved);

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
