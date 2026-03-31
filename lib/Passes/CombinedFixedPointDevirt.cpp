#include "omill/Passes/CombinedFixedPointDevirt.h"

#include <llvm/Analysis/ConstantFolding.h>
#include <llvm/Analysis/InstructionSimplify.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Transforms/Utils/Local.h>

#include <cstdint>
#include <cstring>
#include <optional>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Passes/ConstantMemoryFolding.h"

namespace omill {

namespace {

struct CanonicalAddress {
  llvm::Value *base = nullptr;
  int64_t offset = 0;
};

struct SelectAddressPair {
  llvm::Value *condition = nullptr;
  uint64_t true_address = 0;
  uint64_t false_address = 0;
};

std::optional<int64_t> constantSignedOffset(llvm::Value *V) {
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
    return CI->getSExtValue();
  return std::nullopt;
}

std::optional<uint64_t> resolveConstantIntegerAddress(llvm::Value *V) {
  V = V->stripPointerCasts();

  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
    return CI->getZExtValue();

  if (auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
    switch (I->getOpcode()) {
      case llvm::Instruction::Add: {
        auto lhs = resolveConstantIntegerAddress(I->getOperand(0));
        auto rhs = resolveConstantIntegerAddress(I->getOperand(1));
        if (!lhs || !rhs)
          return std::nullopt;
        return *lhs + *rhs;
      }
      case llvm::Instruction::Sub: {
        auto lhs = resolveConstantIntegerAddress(I->getOperand(0));
        auto rhs = resolveConstantIntegerAddress(I->getOperand(1));
        if (!lhs || !rhs)
          return std::nullopt;
        return *lhs - *rhs;
      }
      case llvm::Instruction::ZExt:
      case llvm::Instruction::SExt:
      case llvm::Instruction::Trunc:
      case llvm::Instruction::BitCast:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::IntToPtr:
        return resolveConstantIntegerAddress(I->getOperand(0));
      default:
        break;
    }
  }

  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
    switch (CE->getOpcode()) {
      case llvm::Instruction::Add: {
        auto lhs = resolveConstantIntegerAddress(CE->getOperand(0));
        auto rhs = resolveConstantIntegerAddress(CE->getOperand(1));
        if (!lhs || !rhs)
          return std::nullopt;
        return *lhs + *rhs;
      }
      case llvm::Instruction::Sub: {
        auto lhs = resolveConstantIntegerAddress(CE->getOperand(0));
        auto rhs = resolveConstantIntegerAddress(CE->getOperand(1));
        if (!lhs || !rhs)
          return std::nullopt;
        return *lhs - *rhs;
      }
      case llvm::Instruction::ZExt:
      case llvm::Instruction::SExt:
      case llvm::Instruction::Trunc:
      case llvm::Instruction::BitCast:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::IntToPtr:
        return resolveConstantIntegerAddress(CE->getOperand(0));
      default:
        break;
    }
  }

  return std::nullopt;
}

std::optional<SelectAddressPair> resolveSelectAddressPair(llvm::Value *V) {
  V = V->stripPointerCasts();

  auto build_pair_from_select = [](llvm::SelectInst *SI, uint64_t true_base,
                                   uint64_t false_base)
      -> std::optional<SelectAddressPair> {
    auto true_addr = resolveConstantIntegerAddress(SI->getTrueValue());
    auto false_addr = resolveConstantIntegerAddress(SI->getFalseValue());
    if (!true_addr || !false_addr)
      return std::nullopt;
    return SelectAddressPair{SI->getCondition(), true_base + *true_addr,
                             false_base + *false_addr};
  };

  if (auto *SI = llvm::dyn_cast<llvm::SelectInst>(V))
    return build_pair_from_select(SI, 0, 0);

  auto try_add_sub_pair =
      [&](llvm::Value *lhs, llvm::Value *rhs, bool is_sub)
      -> std::optional<SelectAddressPair> {
    auto *SI = llvm::dyn_cast<llvm::SelectInst>(lhs);
    auto *other = rhs;
    bool select_on_rhs = false;
    if (!SI) {
      SI = llvm::dyn_cast<llvm::SelectInst>(rhs);
      other = lhs;
      select_on_rhs = true;
    }
    if (!SI)
      return std::nullopt;

    auto base = resolveConstantIntegerAddress(other);
    if (!base)
      return std::nullopt;
    auto true_val = resolveConstantIntegerAddress(SI->getTrueValue());
    auto false_val = resolveConstantIntegerAddress(SI->getFalseValue());
    if (!true_val || !false_val)
      return std::nullopt;

    if (is_sub) {
      if (select_on_rhs) {
        return SelectAddressPair{SI->getCondition(), *base - *true_val,
                                 *base - *false_val};
      }
      return std::nullopt;
    }

    return SelectAddressPair{SI->getCondition(), *base + *true_val,
                             *base + *false_val};
  };

  if (auto *I = llvm::dyn_cast<llvm::Instruction>(V)) {
    switch (I->getOpcode()) {
      case llvm::Instruction::Add:
        return try_add_sub_pair(I->getOperand(0), I->getOperand(1), false);
      case llvm::Instruction::Sub:
        return try_add_sub_pair(I->getOperand(0), I->getOperand(1), true);
      case llvm::Instruction::IntToPtr:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::ZExt:
      case llvm::Instruction::SExt:
      case llvm::Instruction::Trunc:
      case llvm::Instruction::BitCast:
        return resolveSelectAddressPair(I->getOperand(0));
      default:
        break;
    }
  }

  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
    switch (CE->getOpcode()) {
      case llvm::Instruction::Add:
        return try_add_sub_pair(CE->getOperand(0), CE->getOperand(1), false);
      case llvm::Instruction::Sub:
        return try_add_sub_pair(CE->getOperand(0), CE->getOperand(1), true);
      case llvm::Instruction::IntToPtr:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::ZExt:
      case llvm::Instruction::SExt:
      case llvm::Instruction::Trunc:
      case llvm::Instruction::BitCast:
        return resolveSelectAddressPair(CE->getOperand(0));
      default:
        break;
    }
  }

  return std::nullopt;
}

CanonicalAddress canonicalizeIntegerAddress(llvm::Value *V) {
  CanonicalAddress result{V, 0};

  while (auto *I = llvm::dyn_cast<llvm::Instruction>(result.base)) {
    switch (I->getOpcode()) {
      case llvm::Instruction::Add: {
        auto *op0 = I->getOperand(0);
        auto *op1 = I->getOperand(1);
        if (auto imm = constantSignedOffset(op1)) {
          result.offset += *imm;
          result.base = op0;
          continue;
        }
        if (auto imm = constantSignedOffset(op0)) {
          result.offset += *imm;
          result.base = op1;
          continue;
        }
        return result;
      }
      case llvm::Instruction::Sub: {
        auto *op1 = I->getOperand(1);
        if (auto imm = constantSignedOffset(op1)) {
          result.offset -= *imm;
          result.base = I->getOperand(0);
          continue;
        }
        return result;
      }
      case llvm::Instruction::ZExt:
      case llvm::Instruction::SExt:
      case llvm::Instruction::Trunc:
      case llvm::Instruction::BitCast:
      case llvm::Instruction::PtrToInt:
        result.base = I->getOperand(0);
        continue;
      default:
        return result;
    }
  }

  return result;
}

CanonicalAddress canonicalizePointer(llvm::Value *ptr,
                                     const llvm::DataLayout &DL) {
  ptr = ptr->stripPointerCasts();

  if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(ptr)) {
    llvm::APInt ap_offset(DL.getPointerSizeInBits(
                              GEP->getPointerAddressSpace()),
                          0, /*isSigned=*/true);
    if (GEP->accumulateConstantOffset(DL, ap_offset)) {
      auto result = canonicalizePointer(GEP->getPointerOperand(), DL);
      result.offset += ap_offset.getSExtValue();
      return result;
    }
  }

  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr))
    return canonicalizeIntegerAddress(ITP->getOperand(0));

  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr)
      return canonicalizeIntegerAddress(CE->getOperand(0));
  }

  return {ptr, 0};
}

unsigned scalarBitWidth(llvm::Type *Ty, const llvm::DataLayout &DL) {
  if (auto *ITy = llvm::dyn_cast<llvm::IntegerType>(Ty))
    return ITy->getBitWidth();
  if (Ty->isPointerTy())
    return DL.getPointerSizeInBits(Ty->getPointerAddressSpace());
  return 0;
}

llvm::Constant *coerceStoredConstant(llvm::Value *stored_value,
                                     llvm::Type *load_ty,
                                     const llvm::DataLayout &DL) {
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(stored_value)) {
    unsigned dst_bits = scalarBitWidth(load_ty, DL);
    if (dst_bits == 0 || dst_bits > 64)
      return nullptr;
    llvm::APInt ap(CI->getBitWidth(), CI->getZExtValue());
    if (load_ty->isIntegerTy())
      return llvm::ConstantInt::get(load_ty, ap.zextOrTrunc(dst_bits));
    if (load_ty->isPointerTy())
      return llvm::ConstantExpr::getIntToPtr(
          llvm::ConstantInt::get(
              llvm::Type::getIntNTy(load_ty->getContext(), dst_bits),
              ap.zextOrTrunc(dst_bits)),
          load_ty);
  }

  if (load_ty->isPointerTy()) {
    if (llvm::isa<llvm::ConstantPointerNull>(stored_value))
      return llvm::ConstantPointerNull::get(
          llvm::cast<llvm::PointerType>(load_ty));
    if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(stored_value)) {
      if (CE->getOpcode() == llvm::Instruction::IntToPtr &&
          CE->getType() == load_ty)
        return CE;
    }
  }

  return nullptr;
}

bool tryForwardLoadsFromStores(llvm::Function &F, const llvm::DataLayout &DL) {
  bool changed = false;
  llvm::SmallVector<llvm::Instruction *, 16> dead;

  for (auto &BB : F) {
    for (auto it = BB.begin(), end = BB.end(); it != end;) {
      llvm::Instruction &I = *it++;
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || LI->isVolatile())
        continue;

      auto load_bits = scalarBitWidth(LI->getType(), DL);
      if (load_bits == 0)
        continue;

      CanonicalAddress load_addr =
          canonicalizePointer(LI->getPointerOperand(), DL);

      for (auto search = LI->getIterator(); search != BB.begin();) {
        --search;
        auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*search);
        if (!SI || SI->isVolatile())
          continue;
        if (scalarBitWidth(SI->getValueOperand()->getType(), DL) != load_bits)
          continue;

        CanonicalAddress store_addr =
            canonicalizePointer(SI->getPointerOperand(), DL);
        if (store_addr.base != load_addr.base ||
            store_addr.offset != load_addr.offset) {
          continue;
        }

        if (auto *replacement =
                coerceStoredConstant(SI->getValueOperand(), LI->getType(), DL)) {
          LI->replaceAllUsesWith(replacement);
          dead.push_back(LI);
          changed = true;
        }
        break;
      }
    }
  }

  for (llvm::Instruction *I : dead)
    llvm::RecursivelyDeleteTriviallyDeadInstructions(I);

  return changed;
}

std::optional<unsigned> remillReadMemoryByteWidth(llvm::StringRef name) {
  if (!name.starts_with("__remill_read_memory_"))
    return std::nullopt;

  name = name.drop_front(std::strlen("__remill_read_memory_"));
  unsigned bits = 0;
  if (name.getAsInteger(10, bits) || bits == 0 || (bits % 8) != 0)
    return std::nullopt;
  return bits / 8;
}

llvm::Constant *readConstantBits(const BinaryMemoryMap &map, llvm::Type *Ty,
                                 uint64_t addr, const llvm::DataLayout &DL) {
  unsigned bits = scalarBitWidth(Ty, DL);
  if (bits == 0 || bits > 64 || (bits % 8) != 0)
    return nullptr;

  auto raw = map.readInt(addr, bits / 8);
  if (!raw)
    return nullptr;

  if (Ty->isIntegerTy())
    return llvm::ConstantInt::get(Ty, *raw);
  if (Ty->isPointerTy()) {
    auto *int_ty = llvm::Type::getIntNTy(Ty->getContext(), bits);
    return llvm::ConstantExpr::getIntToPtr(llvm::ConstantInt::get(int_ty, *raw),
                                           Ty);
  }
  return nullptr;
}

bool tryConcretizeSelectBasedLoads(llvm::Function &F, const BinaryMemoryMap &map,
                                   const llvm::DataLayout &DL) {
  bool changed = false;
  llvm::SmallVector<llvm::Instruction *, 8> dead;

  for (auto &BB : F) {
    for (auto it = BB.begin(), end = BB.end(); it != end;) {
      llvm::Instruction &I = *it++;

      llvm::Type *load_ty = nullptr;
      std::optional<SelectAddressPair> pair;

      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        load_ty = LI->getType();
        pair = resolveSelectAddressPair(LI->getPointerOperand());
      } else if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        auto *callee = CB->getCalledFunction();
        if (!callee || CB->arg_size() < 2)
          continue;
        auto width = remillReadMemoryByteWidth(callee->getName());
        if (!width)
          continue;
        load_ty = CB->getType();
        pair = resolveSelectAddressPair(CB->getArgOperand(1));
      } else {
        continue;
      }

      if (!load_ty || !pair)
        continue;

      auto *true_const =
          readConstantBits(map, load_ty, pair->true_address, DL);
      auto *false_const =
          readConstantBits(map, load_ty, pair->false_address, DL);
      if (!true_const || !false_const)
        continue;

      llvm::IRBuilder<> B(&I);
      auto *replacement =
          B.CreateSelect(pair->condition, true_const, false_const,
                         I.getName().empty() ? "" : I.getName() + ".sel");
      I.replaceAllUsesWith(replacement);
      dead.push_back(&I);
      changed = true;
    }
  }

  for (llvm::Instruction *I : dead)
    llvm::RecursivelyDeleteTriviallyDeadInstructions(I);

  return changed;
}

bool simplifyInstructions(llvm::Function &F) {
  bool changed = false;
  auto &DL = F.getParent()->getDataLayout();
  llvm::SimplifyQuery SQ(DL);

  llvm::SmallVector<llvm::Instruction *, 16> dead;
  for (auto &BB : F) {
    for (auto it = BB.begin(), end = BB.end(); it != end;) {
      llvm::Instruction &I = *it++;
      if (I.isTerminator() || llvm::isa<llvm::PHINode>(&I))
        continue;

      llvm::Value *replacement = llvm::simplifyInstruction(&I, SQ);
      if (!replacement)
        replacement = llvm::ConstantFoldInstruction(&I, DL);
      if (!replacement || replacement == &I)
        continue;

      I.replaceAllUsesWith(replacement);
      dead.push_back(&I);
      changed = true;
    }
  }

  for (llvm::Instruction *I : dead)
    llvm::RecursivelyDeleteTriviallyDeadInstructions(I);

  return changed;
}

}  // namespace

llvm::PreservedAnalyses CombinedFixedPointDevirtPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  bool changed = false;
  const auto &DL = F.getParent()->getDataLayout();
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());

  for (unsigned round = 0; round < max_rounds_; ++round) {
    bool round_changed = false;

    auto cmf_pa = ConstantMemoryFoldingPass().run(F, AM);
    if (!cmf_pa.areAllPreserved()) {
      round_changed = true;
      changed = true;
    }

    if (tryForwardLoadsFromStores(F, DL)) {
      round_changed = true;
      changed = true;
    }

    if (map && tryConcretizeSelectBasedLoads(F, *map, DL)) {
      round_changed = true;
      changed = true;
    }

    if (simplifyInstructions(F)) {
      round_changed = true;
      changed = true;
    }

    if (!round_changed)
      break;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
