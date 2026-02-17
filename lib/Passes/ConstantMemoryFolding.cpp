#include "omill/Passes/ConstantMemoryFolding.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include "omill/Analysis/BinaryMemoryMap.h"

namespace omill {

namespace {

/// Try to resolve a pointer operand to a constant integer address.
/// Handles:
///   - inttoptr(i64 <const>)  (ConstantExpr or IntToPtrInst)
///   - gep(inttoptr(i64 <const>), <const offsets>)
std::optional<uint64_t> resolveConstantAddress(llvm::Value *ptr,
                                                const llvm::DataLayout &DL) {
  // Strip pointer casts (bitcast, addrspacecast).
  ptr = ptr->stripPointerCasts();

  // Case 1: ConstantExpr inttoptr.
  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr) {
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(CE->getOperand(0)))
        return CI->getZExtValue();
    }
    // GEP constant expression with inttoptr base.
    if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
      auto *GEP = llvm::cast<llvm::GEPOperator>(CE);
      auto base_addr = resolveConstantAddress(GEP->getPointerOperand(), DL);
      if (!base_addr)
        return std::nullopt;
      llvm::APInt offset(DL.getPointerSizeInBits(), 0);
      if (!GEP->accumulateConstantOffset(DL, offset))
        return std::nullopt;
      return *base_addr + offset.getZExtValue();
    }
  }

  // Case 2: IntToPtrInst with constant operand.
  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(ITP->getOperand(0)))
      return CI->getZExtValue();
  }

  // Case 3: GEP instruction with resolvable base.
  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    auto base_addr = resolveConstantAddress(GEP->getPointerOperand(), DL);
    if (!base_addr)
      return std::nullopt;
    llvm::APInt offset(DL.getPointerSizeInBits(), 0);
    if (!GEP->accumulateConstantOffset(DL, offset))
      return std::nullopt;
    return *base_addr + offset.getZExtValue();
  }

  return std::nullopt;
}

}  // namespace

llvm::PreservedAnalyses ConstantMemoryFoldingPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  const auto &DL = F.getDataLayout();
  bool changed = false;

  llvm::SmallVector<llvm::LoadInst *, 16> loads;
  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I))
        loads.push_back(LI);

  // Get or create the !omill.relocated metadata kind.
  auto &Ctx = F.getContext();
  unsigned reloc_md_kind = Ctx.getMDKindID("omill.relocated");
  bool suspicious_base = map->isSuspiciousImageBase();

  for (auto *LI : loads) {
    auto addr = resolveConstantAddress(LI->getPointerOperand(), DL);
    if (!addr)
      continue;

    llvm::Type *ty = LI->getType();
    unsigned bytes = 0;

    if (ty->isIntegerTy()) {
      unsigned bits = ty->getIntegerBitWidth();
      bytes = (bits + 7) / 8;
      if (bytes > 8)
        continue;
    } else if (ty->isFloatTy()) {
      bytes = 4;
    } else if (ty->isDoubleTy()) {
      bytes = 8;
    } else {
      continue;
    }

    auto val = map->readInt(*addr, bytes);
    if (!val)
      continue;

    // Check relocation overlap and classify.
    auto kind = map->classifyRelocatedValue(*addr, bytes, *val);

    if (kind == RelocValueKind::Suspicious) {
      // The value at a relocated address doesn't look like a valid VA.
      // This could be a protector encoding constants via relocations.
      // At preferred base (delta=0), the on-disk value is still correct.
      // If the image base is suspicious, refuse to fold — the delta is
      // likely non-zero and the on-disk value would be wrong.
      if (suspicious_base)
        continue;
    }

    // Fold the value.
    llvm::Value *replacement = nullptr;

    if (ty->isIntegerTy()) {
      replacement = llvm::ConstantInt::get(ty, *val);
    } else if (ty->isFloatTy()) {
      uint32_t bits = static_cast<uint32_t>(*val);
      float fval;
      std::memcpy(&fval, &bits, 4);
      replacement = llvm::ConstantFP::get(ty, static_cast<double>(fval));
    } else if (ty->isDoubleTy()) {
      double dval;
      std::memcpy(&dval, &*val, 8);
      replacement = llvm::ConstantFP::get(ty, dval);
    }

    if (!replacement)
      continue;

    // If the value is relocated, tag the original load's users with metadata
    // before replacing. For integer types, we can directly tag the replacement
    // instruction if there is one. For constants, we use metadata on the
    // load's debug location as a breadcrumb.
    if (kind != RelocValueKind::NotRelocated) {
      // Create metadata: !omill.relocated !{kind_string, original_addr}
      auto *kind_str = llvm::MDString::get(
          Ctx, kind == RelocValueKind::NormalAddress ? "address" : "suspicious");
      auto *addr_val = llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(llvm::Type::getInt64Ty(Ctx), *addr));
      auto *md = llvm::MDNode::get(Ctx, {kind_str, addr_val});

      // Attach to users that are instructions (they survive replacement).
      for (auto *U : LI->users()) {
        if (auto *UI = llvm::dyn_cast<llvm::Instruction>(U))
          UI->setMetadata(reloc_md_kind, md);
      }
    }

    LI->replaceAllUsesWith(replacement);
    LI->eraseFromParent();
    changed = true;
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
