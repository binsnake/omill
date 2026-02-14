#include "omill/Passes/LowerAtomicIntrinsics.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Utils/IntrinsicTable.h"

namespace omill {

namespace {

unsigned getAtomicBitWidth(IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kCompareExchange8:
    case IntrinsicKind::kFetchAndAdd8:
    case IntrinsicKind::kFetchAndSub8:
    case IntrinsicKind::kFetchAndAnd8:
    case IntrinsicKind::kFetchAndOr8:
    case IntrinsicKind::kFetchAndXor8:
    case IntrinsicKind::kFetchAndNand8:
      return 8;
    case IntrinsicKind::kCompareExchange16:
    case IntrinsicKind::kFetchAndAdd16:
    case IntrinsicKind::kFetchAndSub16:
    case IntrinsicKind::kFetchAndAnd16:
    case IntrinsicKind::kFetchAndOr16:
    case IntrinsicKind::kFetchAndXor16:
    case IntrinsicKind::kFetchAndNand16:
      return 16;
    case IntrinsicKind::kCompareExchange32:
    case IntrinsicKind::kFetchAndAdd32:
    case IntrinsicKind::kFetchAndSub32:
    case IntrinsicKind::kFetchAndAnd32:
    case IntrinsicKind::kFetchAndOr32:
    case IntrinsicKind::kFetchAndXor32:
    case IntrinsicKind::kFetchAndNand32:
      return 32;
    case IntrinsicKind::kCompareExchange64:
    case IntrinsicKind::kFetchAndAdd64:
    case IntrinsicKind::kFetchAndSub64:
    case IntrinsicKind::kFetchAndAnd64:
    case IntrinsicKind::kFetchAndOr64:
    case IntrinsicKind::kFetchAndXor64:
    case IntrinsicKind::kFetchAndNand64:
      return 64;
    case IntrinsicKind::kCompareExchange128:
      return 128;
    default:
      return 0;
  }
}

llvm::AtomicRMWInst::BinOp getFetchAndOp(IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kFetchAndAdd8:
    case IntrinsicKind::kFetchAndAdd16:
    case IntrinsicKind::kFetchAndAdd32:
    case IntrinsicKind::kFetchAndAdd64:
      return llvm::AtomicRMWInst::Add;
    case IntrinsicKind::kFetchAndSub8:
    case IntrinsicKind::kFetchAndSub16:
    case IntrinsicKind::kFetchAndSub32:
    case IntrinsicKind::kFetchAndSub64:
      return llvm::AtomicRMWInst::Sub;
    case IntrinsicKind::kFetchAndAnd8:
    case IntrinsicKind::kFetchAndAnd16:
    case IntrinsicKind::kFetchAndAnd32:
    case IntrinsicKind::kFetchAndAnd64:
      return llvm::AtomicRMWInst::And;
    case IntrinsicKind::kFetchAndOr8:
    case IntrinsicKind::kFetchAndOr16:
    case IntrinsicKind::kFetchAndOr32:
    case IntrinsicKind::kFetchAndOr64:
      return llvm::AtomicRMWInst::Or;
    case IntrinsicKind::kFetchAndXor8:
    case IntrinsicKind::kFetchAndXor16:
    case IntrinsicKind::kFetchAndXor32:
    case IntrinsicKind::kFetchAndXor64:
      return llvm::AtomicRMWInst::Xor;
    case IntrinsicKind::kFetchAndNand8:
    case IntrinsicKind::kFetchAndNand16:
    case IntrinsicKind::kFetchAndNand32:
    case IntrinsicKind::kFetchAndNand64:
      return llvm::AtomicRMWInst::Nand;
    default:
      return llvm::AtomicRMWInst::BAD_BINOP;
  }
}

/// Lower __remill_compare_exchange_memory_N(mem, addr, expected_ref, desired)
/// Pattern: expected is passed by reference, updated with old value on failure.
void lowerCompareExchange(llvm::CallInst *CI, unsigned bit_width) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *expected_ref = CI->getArgOperand(2);
  llvm::Value *desired = CI->getArgOperand(3);

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());

  // Load the expected value from the reference
  llvm::Value *expected = Builder.CreateLoad(int_ty, expected_ref);

  // For 128-bit, desired is also passed by reference
  if (bit_width == 128) {
    desired = Builder.CreateLoad(int_ty, desired);
  }

  // Create cmpxchg instruction
  auto *cmpxchg = Builder.CreateAtomicCmpXchg(
      ptr, expected, desired, llvm::MaybeAlign(),
      llvm::AtomicOrdering::SequentiallyConsistent,
      llvm::AtomicOrdering::SequentiallyConsistent);

  // Extract the old value and store it back to expected_ref
  auto *old_val = Builder.CreateExtractValue(cmpxchg, 0);
  Builder.CreateStore(old_val, expected_ref);

  // Replace Memory* return with input Memory*
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower __remill_fetch_and_OP_N(mem, addr, value_ref)
/// Pattern: value is passed by reference, updated with old value.
void lowerFetchAndOp(llvm::CallInst *CI, IntrinsicKind kind,
                     unsigned bit_width) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *value_ref = CI->getArgOperand(2);

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());

  // Load the operand value from the reference
  llvm::Value *value = Builder.CreateLoad(int_ty, value_ref);

  auto binop = getFetchAndOp(kind);

  // Create atomicrmw instruction
  auto *result = Builder.CreateAtomicRMW(
      binop, ptr, value, llvm::MaybeAlign(),
      llvm::AtomicOrdering::SequentiallyConsistent);

  // Store the old value back to the reference
  Builder.CreateStore(result, value_ref);

  // Replace Memory* return with input Memory*
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

}  // namespace

llvm::PreservedAnalyses LowerAtomicIntrinsicsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());

  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 16> pending;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI) continue;

      auto kind = table.classifyCall(CI);
      auto cat = IntrinsicTable::categoryOf(kind);
      if (cat == IntrinsicCategory::kAtomic ||
          cat == IntrinsicCategory::kFetchAndOp) {
        pending.push_back({CI, kind});
      }
    }
  }

  if (pending.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  for (auto &[CI, kind] : pending) {
    switch (kind) {
      case IntrinsicKind::kAtomicBegin:
      case IntrinsicKind::kAtomicEnd: {
        // Replace with input Memory* and remove
        CI->replaceAllUsesWith(CI->getArgOperand(0));
        CI->eraseFromParent();
        break;
      }

      case IntrinsicKind::kCompareExchange8:
      case IntrinsicKind::kCompareExchange16:
      case IntrinsicKind::kCompareExchange32:
      case IntrinsicKind::kCompareExchange64:
      case IntrinsicKind::kCompareExchange128:
        lowerCompareExchange(CI, getAtomicBitWidth(kind));
        break;

      default: {
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kFetchAndOp) {
          lowerFetchAndOp(CI, kind, getAtomicBitWidth(kind));
        }
        break;
      }
    }
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
