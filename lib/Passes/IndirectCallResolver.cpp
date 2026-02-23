#include "omill/Passes/IndirectCallResolver.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Maximum expression tree depth to prevent infinite recursion through PHIs.
static constexpr unsigned kMaxEvalDepth = 16;

/// Recursively evaluate an SSA value to a concrete uint64_t using binary
/// memory reads for loads from constant addresses.
///
/// This is the core of the pass: unlike ConstantMemoryFolding (which folds
/// individual loads) or InstCombine (which folds arithmetic), this evaluator
/// walks the entire expression tree in one shot, resolving multi-hop chains
/// like load(load(0x140008000) + 0x10) without requiring multiple pass
/// iterations.
std::optional<uint64_t> evaluateToConstant(llvm::Value *V,
                                           const BinaryMemoryMap &map,
                                           unsigned depth = 0) {
  if (depth > kMaxEvalDepth)
    return std::nullopt;

  // Already a constant integer.
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    if (CI->getBitWidth() <= 64)
      return CI->getZExtValue();
    return std::nullopt;
  }

  // ZExt / SExt: evaluate the inner value.
  if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(V))
    return evaluateToConstant(zext->getOperand(0), map, depth + 1);
  if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(V)) {
    auto inner = evaluateToConstant(sext->getOperand(0), map, depth + 1);
    if (!inner)
      return std::nullopt;
    unsigned src_bits = sext->getOperand(0)->getType()->getIntegerBitWidth();
    // Sign extend from src_bits to 64 bits.
    uint64_t val = *inner;
    if (src_bits < 64 && (val & (1ULL << (src_bits - 1))))
      val |= ~((1ULL << src_bits) - 1);
    return val;
  }

  // Trunc: evaluate inner and mask.
  if (auto *trunc = llvm::dyn_cast<llvm::TruncInst>(V)) {
    auto inner = evaluateToConstant(trunc->getOperand(0), map, depth + 1);
    if (!inner)
      return std::nullopt;
    unsigned dst_bits = trunc->getType()->getIntegerBitWidth();
    if (dst_bits >= 64)
      return *inner;
    return *inner & ((1ULL << dst_bits) - 1);
  }

  // Binary operators: add, sub, xor, or, and, shl, lshr, ashr, mul.
  if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto lhs = evaluateToConstant(bin->getOperand(0), map, depth + 1);
    auto rhs = evaluateToConstant(bin->getOperand(1), map, depth + 1);
    if (!lhs || !rhs)
      return std::nullopt;

    switch (bin->getOpcode()) {
    case llvm::Instruction::Add:  return *lhs + *rhs;
    case llvm::Instruction::Sub:  return *lhs - *rhs;
    case llvm::Instruction::Mul:  return *lhs * *rhs;
    case llvm::Instruction::Xor:  return *lhs ^ *rhs;
    case llvm::Instruction::Or:   return *lhs | *rhs;
    case llvm::Instruction::And:  return *lhs & *rhs;
    case llvm::Instruction::Shl:  return (*rhs < 64) ? (*lhs << *rhs) : 0ULL;
    case llvm::Instruction::LShr: return (*rhs < 64) ? (*lhs >> *rhs) : 0ULL;
    case llvm::Instruction::AShr: {
      if (*rhs >= 64)
        return (*lhs & (1ULL << 63)) ? ~0ULL : 0ULL;
      return static_cast<uint64_t>(
          static_cast<int64_t>(*lhs) >> static_cast<int64_t>(*rhs));
    }
    default:
      return std::nullopt;
    }
  }

  // Load from a constant address: read from binary memory.
  if (auto *load = llvm::dyn_cast<llvm::LoadInst>(V)) {
    auto *ptr = load->getPointerOperand()->stripPointerCasts();

    // inttoptr(X) — evaluate X to get the address.
    llvm::Value *int_val = nullptr;
    if (auto *itp = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
      int_val = itp->getOperand(0);
    else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
      if (ce->getOpcode() == llvm::Instruction::IntToPtr)
        int_val = ce->getOperand(0);
    }

    if (!int_val)
      return std::nullopt;

    auto addr = evaluateToConstant(int_val, map, depth + 1);
    if (!addr)
      return std::nullopt;

    // Read from binary memory.
    unsigned load_size = load->getType()->getIntegerBitWidth() / 8;
    if (load_size > 8)
      return std::nullopt;

    uint8_t buf[8] = {};
    if (!map.read(*addr, buf, load_size))
      return std::nullopt;

    // Little-endian reassembly.
    uint64_t result = 0;
    for (unsigned i = 0; i < load_size; ++i)
      result |= static_cast<uint64_t>(buf[i]) << (i * 8);

    // Mask to load width.
    unsigned bits = load->getType()->getIntegerBitWidth();
    if (bits < 64)
      result &= (1ULL << bits) - 1;

    return result;
  }

  // Select with one evaluable arm (or both).
  if (auto *sel = llvm::dyn_cast<llvm::SelectInst>(V)) {
    auto cond = evaluateToConstant(sel->getCondition(), map, depth + 1);
    if (cond) {
      // Condition is known — evaluate only the selected arm.
      auto *arm = (*cond != 0) ? sel->getTrueValue() : sel->getFalseValue();
      return evaluateToConstant(arm, map, depth + 1);
    }
    // If both arms evaluate to the same value, use that.
    auto true_val = evaluateToConstant(sel->getTrueValue(), map, depth + 1);
    auto false_val = evaluateToConstant(sel->getFalseValue(), map, depth + 1);
    if (true_val && false_val && *true_val == *false_val)
      return *true_val;
    return std::nullopt;
  }

  // PHI with all evaluable incoming values that agree.
  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(V)) {
    if (phi->getNumIncomingValues() == 0)
      return std::nullopt;
    std::optional<uint64_t> agreed;
    for (unsigned i = 0, e = phi->getNumIncomingValues(); i < e; ++i) {
      auto val = evaluateToConstant(phi->getIncomingValue(i), map, depth + 1);
      if (!val)
        return std::nullopt;
      if (!agreed)
        agreed = val;
      else if (*agreed != *val)
        return std::nullopt;
    }
    return agreed;
  }

  return std::nullopt;
}

/// Check if a dispatch target is already resolved (ptrtoint of a Function).
bool isAlreadyResolved(llvm::Value *target) {
  if (auto *ptoi = llvm::dyn_cast<llvm::PtrToIntOperator>(target))
    if (llvm::isa<llvm::Function>(ptoi->getPointerOperand()))
      return true;
  if (llvm::isa<llvm::ConstantInt>(target))
    return true;
  return false;
}

/// Resolve a dispatch_call target: replace with constant or ptrtoint(@import).
/// Returns true if the call was modified.
bool resolveDispatchCall(llvm::CallInst *call, uint64_t resolved_pc,
                         const BinaryMemoryMap *map,
                         const LiftedFunctionMap *lifted) {
  auto &M = *call->getFunction()->getParent();
  auto &Ctx = call->getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Priority 1: IAT import.
  if (map && map->hasImports()) {
    if (auto *imp = map->lookupImport(resolved_pc)) {
      auto *fn_type = llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false);
      auto fn_callee = M.getOrInsertFunction(imp->function, fn_type);
      auto *fn = llvm::dyn_cast<llvm::Function>(fn_callee.getCallee());
      if (fn) {
        fn->setDLLStorageClass(llvm::GlobalValue::DLLImportStorageClass);
        llvm::IRBuilder<> Builder(call);
        auto *fn_addr = Builder.CreatePtrToInt(fn, i64_ty,
                                               imp->function + ".addr");
        call->setArgOperand(1, fn_addr);
        return true;
      }
    }
  }

  // Priority 2: Direct call to lifted function.
  auto *target_fn = lifted ? lifted->lookup(resolved_pc) : nullptr;
  if (target_fn) {
    llvm::IRBuilder<> Builder(call);
    auto *direct_call = Builder.CreateCall(
        target_fn,
        {call->getArgOperand(0),
         llvm::ConstantInt::get(i64_ty, resolved_pc),
         call->getArgOperand(2)});
    call->replaceAllUsesWith(direct_call);
    call->eraseFromParent();
    return true;
  }

  // Priority 3: Replace target with constant (for downstream passes to handle).
  call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
  return true;
}

/// Resolve a dispatch_jump target.
/// Returns true if the call was modified.
bool resolveDispatchJump(llvm::CallInst *call, uint64_t resolved_pc,
                         const LiftedFunctionMap *lifted) {
  auto *F = call->getFunction();

  // Must be followed by ret.
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(call->getNextNode());
  if (!ret)
    return false;

  auto *BB = call->getParent();
  llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

  // Priority 1: Intra-function branch.
  if (auto *target_bb = findBlockForPC(*F, resolved_pc)) {
    llvm::IRBuilder<> Builder(call);
    auto *br = Builder.CreateBr(target_bb);

    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    ret->eraseFromParent();
    call->eraseFromParent();

    // Clean dead instructions between branch and end of block.
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

    return true;
  }

  // Priority 2: Inter-function musttail call.
  auto *target_fn = lifted ? lifted->lookup(resolved_pc) : nullptr;
  if (target_fn) {
    auto &Ctx = F->getContext();
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

    llvm::IRBuilder<> Builder(call);
    auto *tail_call = Builder.CreateCall(
        target_fn,
        {call->getArgOperand(0),
         llvm::ConstantInt::get(i64_ty, resolved_pc),
         call->getArgOperand(2)});
    tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
    auto *new_ret = Builder.CreateRet(tail_call);

    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    ret->eraseFromParent();
    call->eraseFromParent();

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

    return true;
  }

  // Priority 3: Replace target with constant for downstream passes.
  auto *i64_ty = llvm::Type::getInt64Ty(call->getContext());
  call->setArgOperand(1, llvm::ConstantInt::get(i64_ty, resolved_pc));
  return true;
}

}  // namespace

llvm::PreservedAnalyses IndirectCallResolverPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map)
    return llvm::PreservedAnalyses::all();

  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());

  // Collect candidates: dispatch_call and dispatch_jump with non-constant,
  // non-resolved targets.
  struct Candidate {
    llvm::CallInst *call;
    bool is_jump;
  };
  llvm::SmallVector<Candidate, 8> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;
      if (call->arg_size() < 3)
        continue;

      bool is_call = (callee->getName() == "__omill_dispatch_call");
      bool is_jump = (callee->getName() == "__omill_dispatch_jump");
      if (!is_call && !is_jump)
        continue;

      auto *target = call->getArgOperand(1);
      if (isAlreadyResolved(target))
        continue;

      candidates.push_back({call, is_jump});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  bool changed = false;

  for (auto &cand : candidates) {
    auto *target = cand.call->getArgOperand(1);
    auto resolved = evaluateToConstant(target, *map);
    if (!resolved)
      continue;

    if (cand.is_jump) {
      changed |= resolveDispatchJump(cand.call, *resolved, lifted);
    } else {
      changed |= resolveDispatchCall(cand.call, *resolved, map, lifted);
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
