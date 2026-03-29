#include "omill/Passes/ConstantMemoryFolding.h"

#include <cstdint>
#include <cstring>
#include <optional>

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/Hashing.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SmallString.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/MDBuilder.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/Format.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Utils/LiftedNames.h"

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

struct SymbolicAddress {
  llvm::Value *base = nullptr;
  int64_t offset = 0;
};

llvm::Constant *constantFromBits(llvm::Type *ty, uint64_t bits);

std::optional<unsigned> remillReadMemoryByteWidth(llvm::StringRef name) {
  if (!name.starts_with("__remill_read_memory_"))
    return std::nullopt;

  name = name.drop_front(strlen("__remill_read_memory_"));
  unsigned bits = 0;
  if (name.getAsInteger(10, bits) || bits == 0 || (bits % 8) != 0)
    return std::nullopt;
  return bits / 8;
}

unsigned scalarBitWidth(llvm::Type *ty, const llvm::DataLayout &DL) {
  if (auto *int_ty = llvm::dyn_cast<llvm::IntegerType>(ty))
    return int_ty->getBitWidth();
  if (ty->isFloatTy())
    return 32;
  if (ty->isDoubleTy())
    return 64;
  if (ty->isPointerTy())
    return DL.getPointerSizeInBits(ty->getPointerAddressSpace());
  return 0;
}

std::optional<uint64_t> resolveConstantIntegerValueImpl(
    llvm::Value *V, const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Value *, std::optional<uint64_t>> &cache,
    llvm::SmallPtrSetImpl<llvm::Value *> &visiting);

std::optional<uint64_t> resolveLoadFromLocalAlloca(
    llvm::LoadInst *LI, const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Value *, std::optional<uint64_t>> &cache,
    llvm::SmallPtrSetImpl<llvm::Value *> &visiting) {
  auto *ptr = LI->getPointerOperand()->stripPointerCasts();
  auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(ptr);
  if (!alloca)
    return std::nullopt;

  auto it = LI->getIterator();
  while (it != LI->getParent()->begin()) {
    --it;
    auto *store = llvm::dyn_cast<llvm::StoreInst>(&*it);
    if (!store)
      continue;
    if (store->getPointerOperand()->stripPointerCasts() != alloca)
      continue;
    return resolveConstantIntegerValueImpl(store->getValueOperand(), DL, cache,
                                          visiting);
  }

  return std::nullopt;
}

std::optional<uint64_t> resolveConstantIntegerValueImpl(
    llvm::Value *V, const llvm::DataLayout &DL,
    llvm::DenseMap<llvm::Value *, std::optional<uint64_t>> &cache,
    llvm::SmallPtrSetImpl<llvm::Value *> &visiting) {
  if (auto found = cache.find(V); found != cache.end())
    return found->second;
  if (!visiting.insert(V).second)
    return std::nullopt;

  auto cache_result = [&](std::optional<uint64_t> value) {
    visiting.erase(V);
    cache[V] = value;
    return value;
  };

  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
    return cache_result(CI->getZExtValue());

  if (auto *load = llvm::dyn_cast<llvm::LoadInst>(V))
    return cache_result(resolveLoadFromLocalAlloca(load, DL, cache, visiting));

  if (auto *cast = llvm::dyn_cast<llvm::CastInst>(V)) {
    auto inner = resolveConstantIntegerValueImpl(cast->getOperand(0), DL, cache,
                                                 visiting);
    if (!inner)
      return cache_result(std::nullopt);

    unsigned src_bits = scalarBitWidth(cast->getOperand(0)->getType(), DL);
    unsigned dst_bits = scalarBitWidth(cast->getType(), DL);
    if (src_bits == 0 || dst_bits == 0 || src_bits > 64 || dst_bits > 64)
      return cache_result(std::nullopt);

    llvm::APInt ap(src_bits, *inner);
    switch (cast->getOpcode()) {
      case llvm::Instruction::ZExt:
      case llvm::Instruction::IntToPtr:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::BitCast:
        return cache_result(ap.zextOrTrunc(dst_bits).getZExtValue());
      case llvm::Instruction::SExt:
        return cache_result(ap.sextOrTrunc(dst_bits).getZExtValue());
      case llvm::Instruction::Trunc:
        return cache_result(ap.trunc(dst_bits).getZExtValue());
      default:
        return cache_result(std::nullopt);
    }
  }

  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto lhs = resolveConstantIntegerValueImpl(BO->getOperand(0), DL, cache,
                                               visiting);
    auto rhs = resolveConstantIntegerValueImpl(BO->getOperand(1), DL, cache,
                                               visiting);
    if (!lhs || !rhs)
      return cache_result(std::nullopt);

    unsigned bits = scalarBitWidth(BO->getType(), DL);
    if (bits == 0 || bits > 64)
      return cache_result(std::nullopt);

    llvm::APInt lhs_ap(bits, *lhs);
    llvm::APInt rhs_ap(bits, *rhs);
    switch (BO->getOpcode()) {
      case llvm::Instruction::Add:
        return cache_result((lhs_ap + rhs_ap).getZExtValue());
      case llvm::Instruction::Sub:
        return cache_result((lhs_ap - rhs_ap).getZExtValue());
      case llvm::Instruction::And:
        return cache_result((lhs_ap & rhs_ap).getZExtValue());
      case llvm::Instruction::Or:
        return cache_result((lhs_ap | rhs_ap).getZExtValue());
      case llvm::Instruction::Xor:
        return cache_result((lhs_ap ^ rhs_ap).getZExtValue());
      case llvm::Instruction::Shl:
        return cache_result(
            (lhs_ap.shl(rhs_ap.getLimitedValue(bits))).getZExtValue());
      case llvm::Instruction::LShr:
        return cache_result(
            (lhs_ap.lshr(rhs_ap.getLimitedValue(bits))).getZExtValue());
      case llvm::Instruction::AShr:
        return cache_result(
            (lhs_ap.ashr(rhs_ap.getLimitedValue(bits))).getZExtValue());
      default:
        return cache_result(std::nullopt);
    }
  }

  return cache_result(std::nullopt);
}

std::optional<uint64_t> resolveConstantIntegerValue(llvm::Value *V,
                                                    const llvm::DataLayout &DL) {
  llvm::DenseMap<llvm::Value *, std::optional<uint64_t>> cache;
  llvm::SmallPtrSet<llvm::Value *, 16> visiting;
  return resolveConstantIntegerValueImpl(V, DL, cache, visiting);
}

struct MappedRegionRef {
  uint64_t base = 0;
  size_t size = 0;
  const uint8_t *data = nullptr;
  bool read_only = true;
};

std::optional<MappedRegionRef> findMappedRegionContaining(
    const BinaryMemoryMap &map, uint64_t addr, unsigned min_size) {
  std::optional<MappedRegionRef> result;
  map.forEachRegion([&](uint64_t base, const uint8_t *data, size_t size) {
    if (result)
      return;
    if (addr < base)
      return;
    const uint64_t end = addr + static_cast<uint64_t>(min_size);
    if (end < addr)
      return;
    if (end > base + size)
      return;
    result = MappedRegionRef{base, size, data, map.isReadOnly(base, 1)};
  });
  return result;
}

llvm::GlobalVariable *getOrCreateMappedRegionGlobal(llvm::Module &M,
                                                    MappedRegionRef region) {
  llvm::SmallString<32> name;
  llvm::raw_svector_ostream os(name);
  os << ".omill.rodata.0x" << llvm::format_hex_no_prefix(region.base, 1);

  if (auto *existing = M.getGlobalVariable(name))
    return existing;

  auto *init = llvm::ConstantDataArray::get(
      M.getContext(),
      llvm::ArrayRef<uint8_t>(region.data, region.size));
  auto *GV = new llvm::GlobalVariable(
      M, init->getType(), /*isConstant=*/region.read_only,
      llvm::GlobalValue::PrivateLinkage, init, name);
  GV->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
  GV->setAlignment(llvm::Align(1));
  return GV;
}

llvm::Constant *readMappedConstant(llvm::Type *ty, uint64_t addr,
                                   unsigned bytes, const BinaryMemoryMap &map,
                                   bool suspicious_base) {
  if (!map.isReadOnly(addr, bytes))
    return nullptr;

  auto val = map.readInt(addr, bytes);
  if (!val)
    return nullptr;

  auto kind = map.classifyRelocatedValue(addr, bytes, *val);
  if (kind == RelocValueKind::Suspicious && suspicious_base)
    return nullptr;

  return constantFromBits(ty, *val);
}

/// Resolve integer expression into (base + const_offset).
/// Examples:
///   add i64 %rsp, -56   -> {base=%rsp, offset=-56}
///   sub i64 %x, 8       -> {base=%x, offset=-8}
///   i64 %x              -> {base=%x, offset=0}
std::optional<SymbolicAddress> resolveBasePlusConst(llvm::Value *V) {
  if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    if (BO->getOpcode() == llvm::Instruction::Add ||
        BO->getOpcode() == llvm::Instruction::Sub) {
      auto add_const = [&](llvm::Value *lhs, llvm::ConstantInt *rhs,
                           bool negate_rhs) -> std::optional<SymbolicAddress> {
        auto lhs_addr = resolveBasePlusConst(lhs);
        if (!lhs_addr)
          return std::nullopt;
        int64_t c = rhs->getSExtValue();
        lhs_addr->offset += negate_rhs ? -c : c;
        return lhs_addr;
      };

      if (auto *CRHS = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1))) {
        return add_const(BO->getOperand(0), CRHS,
                         BO->getOpcode() == llvm::Instruction::Sub);
      }
      if (BO->getOpcode() == llvm::Instruction::Add) {
        if (auto *CLHS =
                llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(0))) {
          return add_const(BO->getOperand(1), CLHS, false);
        }
      }
    }
  }

  // Base value with zero offset.
  return SymbolicAddress{V, 0};
}

/// Resolve pointer into (base + const_offset) when possible.
/// Handles:
///   inttoptr(base + const)
///   gep(inttoptr(base + const), const)
std::optional<SymbolicAddress> resolveSymbolicAddress(llvm::Value *ptr,
                                                      const llvm::DataLayout &DL) {
  ptr = ptr->stripPointerCasts();

  if (auto *CE = llvm::dyn_cast<llvm::ConstantExpr>(ptr)) {
    if (CE->getOpcode() == llvm::Instruction::IntToPtr) {
      return resolveBasePlusConst(CE->getOperand(0));
    }
    if (CE->getOpcode() == llvm::Instruction::GetElementPtr) {
      auto *GEP = llvm::cast<llvm::GEPOperator>(CE);
      auto base = resolveSymbolicAddress(GEP->getPointerOperand(), DL);
      if (!base)
        return std::nullopt;
      llvm::APInt gep_off(DL.getPointerSizeInBits(), 0);
      if (!GEP->accumulateConstantOffset(DL, gep_off))
        return std::nullopt;
      base->offset += gep_off.getSExtValue();
      return base;
    }
    return std::nullopt;
  }

  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    return resolveBasePlusConst(ITP->getOperand(0));
  }

  if (auto *GEP = llvm::dyn_cast<llvm::GetElementPtrInst>(ptr)) {
    auto base = resolveSymbolicAddress(GEP->getPointerOperand(), DL);
    if (!base)
      return std::nullopt;
    llvm::APInt gep_off(DL.getPointerSizeInBits(), 0);
    if (!GEP->accumulateConstantOffset(DL, gep_off))
      return std::nullopt;
    base->offset += gep_off.getSExtValue();
    return base;
  }

  return std::nullopt;
}

struct ByteKey {
  const llvm::Value *base = nullptr;
  int64_t offset = 0;
  bool operator==(const ByteKey &o) const {
    return base == o.base && offset == o.offset;
  }
};

struct ByteKeyInfo {
  static inline ByteKey getEmptyKey() {
    return ByteKey{llvm::DenseMapInfo<const llvm::Value *>::getEmptyKey(), 0};
  }
  static inline ByteKey getTombstoneKey() {
    return ByteKey{llvm::DenseMapInfo<const llvm::Value *>::getTombstoneKey(), 0};
  }
  static unsigned getHashValue(const ByteKey &k) {
    return llvm::hash_combine(k.base, k.offset);
  }
  static bool isEqual(const ByteKey &a, const ByteKey &b) { return a == b; }
};

std::optional<unsigned> loadOrStoreByteWidth(llvm::Type *ty) {
  if (ty->isIntegerTy()) {
    unsigned bits = ty->getIntegerBitWidth();
    unsigned bytes = (bits + 7) / 8;
    if (bytes > 8)
      return std::nullopt;
    return bytes;
  }
  if (ty->isFloatTy())
    return 4;
  if (ty->isDoubleTy())
    return 8;
  return std::nullopt;
}

std::optional<uint64_t> constantScalarBits(llvm::Value *v, llvm::Type *ty) {
  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(v)) {
    return CI->getZExtValue();
  }
  if (auto *CF = llvm::dyn_cast<llvm::ConstantFP>(v)) {
    if (ty->isFloatTy()) {
      auto bits = CF->getValueAPF().bitcastToAPInt().getZExtValue();
      return static_cast<uint32_t>(bits);
    }
    if (ty->isDoubleTy()) {
      return CF->getValueAPF().bitcastToAPInt().getZExtValue();
    }
  }
  return std::nullopt;
}

llvm::Constant *constantFromBits(llvm::Type *ty, uint64_t bits) {
  if (ty->isIntegerTy())
    return llvm::ConstantInt::get(ty, bits);
  if (ty->isFloatTy()) {
    uint32_t b = static_cast<uint32_t>(bits);
    float f;
    std::memcpy(&f, &b, 4);
    return llvm::ConstantFP::get(ty, static_cast<double>(f));
  }
  if (ty->isDoubleTy()) {
    double d;
    std::memcpy(&d, &bits, 8);
    return llvm::ConstantFP::get(ty, d);
  }
  return nullptr;
}

}  // namespace

llvm::PreservedAnalyses ConstantMemoryFoldingPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration())
    return llvm::PreservedAnalyses::all();

  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto *map = MAMProxy.getCachedResult<BinaryMemoryAnalysis>(*F.getParent());
  if (!map || map->empty())
    return llvm::PreservedAnalyses::all();

  const auto &DL = F.getDataLayout();
  bool changed = false;
  auto resolveKnownImageBase =
      [&](llvm::Value *base) -> std::optional<uint64_t> {
    if (auto direct = resolveConstantIntegerValue(base, DL))
      return direct;

    auto *arg = llvm::dyn_cast<llvm::Argument>(base);
    if (!arg || arg->getParent() != &F || arg->getArgNo() != 1)
      return std::nullopt;

    uint64_t entry_va = extractEntryVA(F.getName());
    if (!entry_va)
      return std::nullopt;

    return entry_va;
  };
  std::function<std::optional<uint64_t>(llvm::Value *)>
      resolveKnownConstantIntegerValue =
          [&](llvm::Value *V) -> std::optional<uint64_t> {
    if (auto direct = resolveKnownImageBase(V))
      return direct;

    if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V))
      return CI->getZExtValue();

    if (auto *load = llvm::dyn_cast<llvm::LoadInst>(V)) {
      auto *ptr = load->getPointerOperand()->stripPointerCasts();
      auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(ptr);
      if (!alloca)
        return std::nullopt;

      auto it = load->getIterator();
      while (it != load->getParent()->begin()) {
        --it;
        auto *store = llvm::dyn_cast<llvm::StoreInst>(&*it);
        if (!store)
          continue;
        if (store->getPointerOperand()->stripPointerCasts() != alloca)
          continue;
        return resolveKnownConstantIntegerValue(store->getValueOperand());
      }
      return std::nullopt;
    }

    if (auto *cast = llvm::dyn_cast<llvm::CastInst>(V)) {
      auto inner = resolveKnownConstantIntegerValue(cast->getOperand(0));
      if (!inner)
        return std::nullopt;

      unsigned src_bits = scalarBitWidth(cast->getOperand(0)->getType(), DL);
      unsigned dst_bits = scalarBitWidth(cast->getType(), DL);
      if (src_bits == 0 || dst_bits == 0 || src_bits > 64 || dst_bits > 64)
        return std::nullopt;

      llvm::APInt ap(src_bits, *inner);
      switch (cast->getOpcode()) {
        case llvm::Instruction::ZExt:
        case llvm::Instruction::IntToPtr:
        case llvm::Instruction::PtrToInt:
        case llvm::Instruction::BitCast:
          return ap.zextOrTrunc(dst_bits).getZExtValue();
        case llvm::Instruction::SExt:
          return ap.sextOrTrunc(dst_bits).getZExtValue();
        case llvm::Instruction::Trunc:
          return ap.trunc(dst_bits).getZExtValue();
        default:
          return std::nullopt;
      }
    }

    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
      auto lhs = resolveKnownConstantIntegerValue(BO->getOperand(0));
      auto rhs = resolveKnownConstantIntegerValue(BO->getOperand(1));
      if (!lhs || !rhs)
        return std::nullopt;

      unsigned bits = scalarBitWidth(BO->getType(), DL);
      if (bits == 0 || bits > 64)
        return std::nullopt;

      llvm::APInt lhs_ap(bits, *lhs);
      llvm::APInt rhs_ap(bits, *rhs);
      switch (BO->getOpcode()) {
        case llvm::Instruction::Add:
          return (lhs_ap + rhs_ap).getZExtValue();
        case llvm::Instruction::Sub:
          return (lhs_ap - rhs_ap).getZExtValue();
        case llvm::Instruction::And:
          return (lhs_ap & rhs_ap).getZExtValue();
        case llvm::Instruction::Or:
          return (lhs_ap | rhs_ap).getZExtValue();
        case llvm::Instruction::Xor:
          return (lhs_ap ^ rhs_ap).getZExtValue();
        case llvm::Instruction::Shl:
          return (lhs_ap.shl(rhs_ap.getLimitedValue(bits))).getZExtValue();
        case llvm::Instruction::LShr:
          return (lhs_ap.lshr(rhs_ap.getLimitedValue(bits))).getZExtValue();
        case llvm::Instruction::AShr:
          return (lhs_ap.ashr(rhs_ap.getLimitedValue(bits))).getZExtValue();
        default:
          return std::nullopt;
      }
    }

    return std::nullopt;
  };

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

    if (!map->isReadOnly(*addr, bytes))
      continue;

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

  llvm::SmallVector<llvm::CallInst *, 16> folded_reads;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call || call->arg_size() < 2)
        continue;

      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;

      auto width = remillReadMemoryByteWidth(callee->getName());
      if (!width)
        continue;

      auto addr = resolveKnownConstantIntegerValue(call->getArgOperand(1));
      if (!addr)
        continue;

      auto *replacement =
          readMappedConstant(call->getType(), *addr, *width, *map, suspicious_base);
      if (!replacement)
        continue;

      call->replaceAllUsesWith(replacement);
      folded_reads.push_back(call);
      changed = true;
    }
  }
  for (auto *call : folded_reads)
    call->eraseFromParent();

  llvm::SmallVector<llvm::LoadInst *, 16> constant_region_rewritten_loads;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI)
        continue;

      auto addr = resolveConstantAddress(LI->getPointerOperand(), DL);
      if (!addr)
        continue;

      auto width = loadOrStoreByteWidth(LI->getType());
      if (!width)
        continue;

      auto region = findMappedRegionContaining(*map, *addr, *width);
      if (!region)
        continue;

      auto *GV = getOrCreateMappedRegionGlobal(*F.getParent(), *region);
      llvm::IRBuilder<> B(LI);
      auto *arr_ty = llvm::cast<llvm::ArrayType>(GV->getValueType());
      auto *region_start = B.CreateInBoundsGEP(
          arr_ty, GV, {B.getInt64(0), B.getInt64(0)},
          LI->getName() + ".const.start");
      auto *rewritten_ptr = B.CreateInBoundsGEP(
          B.getInt8Ty(), region_start,
          B.getInt64(*addr - region->base),
          LI->getName() + ".const.ptr");
      auto *rewritten_load = B.CreateLoad(LI->getType(), rewritten_ptr);
      rewritten_load->setAlignment(LI->getAlign());
      rewritten_load->copyMetadata(*LI);
      LI->replaceAllUsesWith(rewritten_load);
      constant_region_rewritten_loads.push_back(LI);
      changed = true;
    }
  }
  for (auto *LI : constant_region_rewritten_loads)
    LI->eraseFromParent();

  llvm::SmallVector<llvm::LoadInst *, 16> image_relative_rewritten_loads;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI)
        continue;

      if (resolveConstantAddress(LI->getPointerOperand(), DL))
        continue;

      auto sym_addr = resolveSymbolicAddress(LI->getPointerOperand(), DL);
      if (!sym_addr || !sym_addr->base)
        continue;

      auto base_addr = resolveKnownImageBase(sym_addr->base);
      if (!base_addr)
        continue;

      auto width = loadOrStoreByteWidth(LI->getType());
      if (!width)
        continue;

      const int64_t signed_offset = sym_addr->offset;
      uint64_t absolute_addr = *base_addr;
      if (signed_offset >= 0) {
        absolute_addr += static_cast<uint64_t>(signed_offset);
      } else {
        uint64_t delta = static_cast<uint64_t>(-signed_offset);
        if (delta > absolute_addr)
          continue;
        absolute_addr -= delta;
      }

      auto region = findMappedRegionContaining(*map, absolute_addr, *width);
      if (!region)
        continue;

      auto *GV = getOrCreateMappedRegionGlobal(*F.getParent(), *region);
      llvm::IRBuilder<> B(LI);
      auto *arr_ty = llvm::cast<llvm::ArrayType>(GV->getValueType());
      auto *region_start = B.CreateInBoundsGEP(
          arr_ty, GV, {B.getInt64(0), B.getInt64(0)},
          LI->getName() + ".img.start");
      auto *rewritten_ptr = B.CreateInBoundsGEP(
          B.getInt8Ty(), region_start,
          B.getInt64(absolute_addr - region->base),
          LI->getName() + ".img.ptr");
      auto *rewritten_load = B.CreateLoad(LI->getType(), rewritten_ptr);
      rewritten_load->setAlignment(LI->getAlign());
      rewritten_load->copyMetadata(*LI);
      LI->replaceAllUsesWith(rewritten_load);
      image_relative_rewritten_loads.push_back(LI);
      changed = true;
    }
  }
  for (auto *LI : image_relative_rewritten_loads)
    LI->eraseFromParent();

  llvm::SmallVector<llvm::LoadInst *, 16> region_rewritten_loads;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI)
        continue;

      if (resolveConstantAddress(LI->getPointerOperand(), DL))
        continue;

      auto sym_addr = resolveSymbolicAddress(LI->getPointerOperand(), DL);
      if (!sym_addr || !sym_addr->base || sym_addr->offset < 0)
        continue;

      if (llvm::isa<llvm::ConstantInt>(sym_addr->base))
        continue;

      auto width = loadOrStoreByteWidth(LI->getType());
      if (!width)
        continue;

      const uint64_t anchor_addr = static_cast<uint64_t>(sym_addr->offset);
      if (!map->isReadOnly(anchor_addr, *width))
        continue;

      auto region = findMappedRegionContaining(*map, anchor_addr, *width);
      if (!region)
        continue;

      auto *GV = getOrCreateMappedRegionGlobal(*F.getParent(), *region);
      llvm::IRBuilder<> B(LI);
      auto *arr_ty = llvm::cast<llvm::ArrayType>(GV->getValueType());
      auto *region_start = B.CreateInBoundsGEP(
          arr_ty, GV,
          {B.getInt64(0), B.getInt64(0)},
          GV->getName() + ".start");

      llvm::Value *base_index = sym_addr->base;
      if (base_index->getType()->isPointerTy()) {
        base_index = B.CreatePtrToInt(base_index, B.getInt64Ty(),
                                      LI->getName() + ".ro.base");
      } else if (base_index->getType()->isIntegerTy()) {
        base_index = B.CreateIntCast(base_index, B.getInt64Ty(),
                                     /*isSigned=*/false,
                                     LI->getName() + ".ro.base");
      } else {
        continue;
      }

      uint64_t region_delta = anchor_addr - region->base;
      llvm::Value *byte_offset = base_index;
      if (region_delta != 0) {
        byte_offset = B.CreateAdd(
            byte_offset, B.getInt64(region_delta),
            LI->getName() + ".ro.off");
      }

      auto *rewritten_ptr = B.CreateInBoundsGEP(
          B.getInt8Ty(), region_start, byte_offset,
          LI->getName() + ".ro.ptr");
      auto *rewritten_load = B.CreateLoad(LI->getType(), rewritten_ptr);
      rewritten_load->setAlignment(LI->getAlign());
      rewritten_load->copyMetadata(*LI);
      LI->replaceAllUsesWith(rewritten_load);
      region_rewritten_loads.push_back(LI);
      changed = true;
    }
  }
  for (auto *LI : region_rewritten_loads)
    LI->eraseFromParent();

  // Local fold: track constant bytes for stack-like symbolic addresses
  // (inttoptr(base + const)) and fold subsequent scalar loads.
  llvm::SmallVector<llvm::LoadInst *, 16> local_folded_loads;
  for (auto &BB : F) {
    llvm::DenseMap<ByteKey, uint8_t, ByteKeyInfo> local_const_bytes;
    for (auto &I : BB) {
      if (auto *CB = llvm::dyn_cast<llvm::CallBase>(&I)) {
        // Basic-block local mode: do not propagate constants across calls.
        if (!CB->onlyReadsMemory()) {
          local_const_bytes.clear();
        }
        continue;
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto addr = resolveSymbolicAddress(SI->getPointerOperand(), DL);
        if (!addr) {
          // Unknown memory write: invalidate tracked bytes.
          local_const_bytes.clear();
          continue;
        }

        auto width = loadOrStoreByteWidth(SI->getValueOperand()->getType());
        if (!width)
          continue;

        auto bits = constantScalarBits(SI->getValueOperand(),
                                       SI->getValueOperand()->getType());
        for (unsigned i = 0; i < *width; ++i) {
          ByteKey key{addr->base, addr->offset + static_cast<int64_t>(i)};
          if (bits) {
            local_const_bytes[key] = static_cast<uint8_t>((*bits >> (8 * i)) & 0xff);
          } else {
            local_const_bytes.erase(key);
          }
        }
        continue;
      }

      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI)
        continue;

      auto addr = resolveSymbolicAddress(LI->getPointerOperand(), DL);
      if (!addr)
        continue;

      auto width = loadOrStoreByteWidth(LI->getType());
      if (!width)
        continue;

      uint64_t bits = 0;
      bool all_present = true;
      for (unsigned i = 0; i < *width; ++i) {
        ByteKey key{addr->base, addr->offset + static_cast<int64_t>(i)};
        auto it = local_const_bytes.find(key);
        if (it == local_const_bytes.end()) {
          all_present = false;
          break;
        }
        bits |= static_cast<uint64_t>(it->second) << (8 * i);
      }
      if (!all_present)
        continue;

      if (auto *C = constantFromBits(LI->getType(), bits)) {
        LI->replaceAllUsesWith(C);
        local_folded_loads.push_back(LI);
        changed = true;
      }
    }
  }
  for (auto *LI : local_folded_loads) {
    LI->eraseFromParent();
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
