#include "omill/Passes/LowerRemillIntrinsics.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/IntrinsicTable.h"
#include "omill/Utils/LiftedNames.h"

#include <cstdlib>

namespace omill {

namespace {

bool debugJumpSelector() {
  static const bool enabled = [] {
    const char *v = std::getenv("OMILL_DEBUG_JUMP_SELECTOR");
    if (!v || v[0] == '\0')
      return false;
    return (v[0] == '1' && v[1] == '\0') || (v[0] == 't' && v[1] == '\0') ||
           (v[0] == 'T' && v[1] == '\0');
  }();
  return enabled;
}

llvm::GlobalVariable *getOrCreateFEnvI32Global(llvm::Module &M,
                                               llvm::StringRef name) {
  if (auto *GV = M.getNamedGlobal(name))
    return GV;
  auto *Ty = llvm::Type::getInt32Ty(M.getContext());
  auto *Init = llvm::ConstantInt::get(Ty, 0);
  auto *GV = new llvm::GlobalVariable(M, Ty,
                                      /*isConstant=*/false,
                                      llvm::GlobalValue::InternalLinkage,
                                      Init, name);
  GV->setUnnamedAddr(llvm::GlobalValue::UnnamedAddr::Global);
  GV->setAlignment(llvm::MaybeAlign(4));
  return GV;
}

llvm::CallInst *createFP80RoundToIntegral(llvm::IRBuilder<> &Builder,
                                          llvm::Value *input) {
  auto *Ty = llvm::Type::getX86_FP80Ty(Builder.getContext());
  auto *FT = llvm::FunctionType::get(Ty, {Ty}, false);
  auto *IA = llvm::InlineAsm::get(
      FT, "frndint", "={st},0,~{fpsr},~{flags}",
      /*hasSideEffects=*/true);
  return Builder.CreateCall(IA, {input});
}

bool isNearbyIntFP80Intrinsic(const llvm::CallInst *CI) {
  auto *callee = CI->getCalledFunction();
  if (!callee)
    return false;
  return callee->getName() == "llvm.nearbyint.f80" &&
         CI->getType()->isX86_FP80Ty();
}

void eraseUnusedLoweringHelperDeclarations(llvm::Module &M) {
  static constexpr llvm::StringLiteral kHelperNames[] = {
      "fetestexcept", "feclearexcept", "feraiseexcept",
      "fesetround",   "fegetround",    "nearbyintl"};
  for (auto name : kHelperNames) {
    if (auto *F = M.getFunction(name); F && F->isDeclaration() &&
                                       F->use_empty()) {
      F->eraseFromParent();
    }
  }
}

// ===----------------------------------------------------------------------===
// Category 1: Flags — replace flag computation/comparison calls with arg0
// ===----------------------------------------------------------------------===

bool lowerFlagIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 32> to_lower;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto cat = IntrinsicTable::categoryOf(table.classifyCall(CI));
        if (cat == IntrinsicCategory::kFlag ||
            cat == IntrinsicCategory::kComparison)
          to_lower.push_back(CI);
      }

  if (to_lower.empty())
    return false;

  for (auto *CI : to_lower) {
    CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 2: Barriers — remove volatile inline asm and barrier intrinsics
// ===----------------------------------------------------------------------===

bool removeBarriers(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 32> to_remove;

  for (auto &BB : F)
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;

      if (CI->isInlineAsm()) {
        if (auto *IA =
                llvm::dyn_cast<llvm::InlineAsm>(CI->getCalledOperand())) {
          auto asm_str = IA->getAsmString();
          if (asm_str.empty() && IA->hasSideEffects()) {
            to_remove.push_back(CI);
          } else if (asm_str == "int1" || asm_str == "int $1") {
            // Remill emits "int1" or "int $1" for x86 ICEBP (opcode 0xF1)
            // which the integrated assembler doesn't recognize.  Replace
            // with the raw byte encoding.
            auto *fixed = llvm::InlineAsm::get(
                IA->getFunctionType(), ".byte 0xf1",
                IA->getConstraintString(), IA->hasSideEffects(),
                IA->isAlignStack(), IA->getDialect());
            CI->setCalledOperand(fixed);
          }
        }
        continue;
      }

      auto kind = table.classifyCall(CI);
      switch (kind) {
        case IntrinsicKind::kBarrierLoadLoad:
        case IntrinsicKind::kBarrierLoadStore:
        case IntrinsicKind::kBarrierStoreLoad:
        case IntrinsicKind::kBarrierStoreStore:
        case IntrinsicKind::kDelaySlotBegin:
        case IntrinsicKind::kDelaySlotEnd:
          to_remove.push_back(CI);
          break;
        default:
          break;
      }
    }

  if (to_remove.empty())
    return false;

  for (auto *CI : to_remove) {
    if (!CI->getType()->isVoidTy() && CI->arg_size() > 0)
      CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 3: Memory — lower read/write memory intrinsics to load/store
// ===----------------------------------------------------------------------===

llvm::Type *getValueType(llvm::LLVMContext &Ctx, IntrinsicKind kind) {
  switch (kind) {
    case IntrinsicKind::kReadMemory8:
    case IntrinsicKind::kWriteMemory8:
      return llvm::Type::getInt8Ty(Ctx);
    case IntrinsicKind::kReadMemory16:
    case IntrinsicKind::kWriteMemory16:
      return llvm::Type::getInt16Ty(Ctx);
    case IntrinsicKind::kReadMemory32:
    case IntrinsicKind::kWriteMemory32:
      return llvm::Type::getInt32Ty(Ctx);
    case IntrinsicKind::kReadMemory64:
    case IntrinsicKind::kWriteMemory64:
      return llvm::Type::getInt64Ty(Ctx);
    case IntrinsicKind::kReadMemoryF32:
    case IntrinsicKind::kWriteMemoryF32:
      return llvm::Type::getFloatTy(Ctx);
    case IntrinsicKind::kReadMemoryF64:
    case IntrinsicKind::kWriteMemoryF64:
      return llvm::Type::getDoubleTy(Ctx);
    case IntrinsicKind::kReadMemoryF80:
    case IntrinsicKind::kWriteMemoryF80:
      return llvm::Type::getX86_FP80Ty(Ctx);
    case IntrinsicKind::kReadMemoryF128:
    case IntrinsicKind::kWriteMemoryF128:
      return llvm::Type::getFP128Ty(Ctx);
    default:
      return nullptr;
  }
}

void lowerReadMemory(llvm::CallInst *CI, IntrinsicKind kind) {
  auto &Ctx = CI->getContext();
  llvm::IRBuilder<> Builder(CI);

  llvm::Type *val_type = getValueType(Ctx, kind);
  if (!val_type)
    return;

  llvm::Value *addr = CI->getArgOperand(1);

  if (kind == IntrinsicKind::kReadMemoryF80) {
    llvm::Value *out_ref = CI->getArgOperand(2);
    llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
    llvm::Value *loaded = Builder.CreateLoad(val_type, ptr);
    Builder.CreateStore(loaded, out_ref);
    CI->replaceAllUsesWith(CI->getArgOperand(0));
    CI->eraseFromParent();
    return;
  }

  llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
  llvm::Value *loaded = Builder.CreateLoad(val_type, ptr);
  CI->replaceAllUsesWith(loaded);
  CI->eraseFromParent();
}

void lowerWriteMemory(llvm::CallInst *CI, IntrinsicKind kind) {
  auto &Ctx = CI->getContext();
  llvm::IRBuilder<> Builder(CI);

  llvm::Type *val_type = getValueType(Ctx, kind);
  if (!val_type)
    return;

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *val = CI->getArgOperand(2);

  if (kind == IntrinsicKind::kWriteMemoryF80) {
    llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
    llvm::Value *loaded_val = Builder.CreateLoad(val_type, val);
    Builder.CreateStore(loaded_val, ptr);
    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();
    return;
  }

  llvm::Value *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());
  Builder.CreateStore(val, ptr);
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

bool lowerMemoryIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 32> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kMemoryRead ||
            cat == IntrinsicCategory::kMemoryWrite)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  for (auto &[CI, kind] : pending) {
    if (IntrinsicTable::categoryOf(kind) == IntrinsicCategory::kMemoryRead)
      lowerReadMemory(CI, kind);
    else
      lowerWriteMemory(CI, kind);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 4: Atomics — lower atomic operations
// ===----------------------------------------------------------------------===

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

void lowerCompareExchange(llvm::CallInst *CI, unsigned bit_width) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *expected_ref = CI->getArgOperand(2);
  llvm::Value *desired = CI->getArgOperand(3);

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());

  llvm::Value *expected = Builder.CreateLoad(int_ty, expected_ref);

  if (bit_width == 128)
    desired = Builder.CreateLoad(int_ty, desired);

  auto *cmpxchg = Builder.CreateAtomicCmpXchg(
      ptr, expected, desired, llvm::Align(bit_width / 8),
      llvm::AtomicOrdering::SequentiallyConsistent,
      llvm::AtomicOrdering::SequentiallyConsistent);

  auto *old_val = Builder.CreateExtractValue(cmpxchg, 0);
  Builder.CreateStore(old_val, expected_ref);

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void lowerFetchAndOp(llvm::CallInst *CI, IntrinsicKind kind,
                     unsigned bit_width) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *mem = CI->getArgOperand(0);
  llvm::Value *addr = CI->getArgOperand(1);
  llvm::Value *value_ref = CI->getArgOperand(2);

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *ptr = Builder.CreateIntToPtr(addr, Builder.getPtrTy());

  llvm::Value *value = Builder.CreateLoad(int_ty, value_ref);

  auto binop = getFetchAndOp(kind);

  auto *result = Builder.CreateAtomicRMW(
      binop, ptr, value, llvm::MaybeAlign(),
      llvm::AtomicOrdering::SequentiallyConsistent);

  Builder.CreateStore(result, value_ref);

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

bool lowerAtomicIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 16> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kAtomic ||
            cat == IntrinsicCategory::kFetchAndOp)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  for (auto &[CI, kind] : pending) {
    switch (kind) {
      case IntrinsicKind::kAtomicBegin:
      case IntrinsicKind::kAtomicEnd:
        CI->replaceAllUsesWith(CI->getArgOperand(0));
        CI->eraseFromParent();
        break;
      case IntrinsicKind::kCompareExchange8:
      case IntrinsicKind::kCompareExchange16:
      case IntrinsicKind::kCompareExchange32:
      case IntrinsicKind::kCompareExchange64:
      case IntrinsicKind::kCompareExchange128:
        lowerCompareExchange(CI, getAtomicBitWidth(kind));
        break;
      default:
        if (IntrinsicTable::categoryOf(kind) == IntrinsicCategory::kFetchAndOp)
          lowerFetchAndOp(CI, kind, getAtomicBitWidth(kind));
        break;
    }
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 5: HyperCalls — CPUID, RDTSC, async, IO, FPU, x86-specific
// ===----------------------------------------------------------------------===

llvm::FunctionCallee getOrDeclareHelper(llvm::Module &M, llvm::StringRef name,
                                         llvm::FunctionType *FT) {
  if (auto *F = M.getFunction(name))
    return F;
  return M.getOrInsertFunction(name, FT);
}

enum SyncHyperCallID : uint32_t {
  kAssertPrivileged = 1,
  kX86EmulateInstruction = 256,
  kAMD64EmulateInstruction = 257,
  kX86CPUID = 258,
  kX86ReadTSC = 259,
  kX86ReadTSCP = 260,
  kX86LoadGlobalDescriptorTable = 261,
  kX86LoadInterruptDescriptorTable = 262,
  kX86ReadModelSpecificRegister = 263,
  kX86WriteModelSpecificRegister = 264,
  kX86WriteBackInvalidate = 265,
  kX86SetSegmentES = 266,
  kX86SetSegmentSS = 267,
  kX86SetSegmentDS = 268,
  kX86SetSegmentFS = 269,
  kX86SetSegmentGS = 270,
  kX86SetDebugReg = 271,
  kAMD64SetDebugReg = 272,
  kX86SetControlReg0 = 273,
  kX86SetControlReg1 = 274,
  kX86SetControlReg2 = 275,
  kX86SetControlReg3 = 276,
  kX86SetControlReg4 = 277,
  kAMD64SetControlReg0 = 278,
  kAMD64SetControlReg1 = 279,
  kAMD64SetControlReg2 = 280,
  kAMD64SetControlReg3 = 281,
  kAMD64SetControlReg4 = 282,
  kAMD64SetControlReg8 = 283,
  kX86SysCall = 284,
  kX86SysEnter = 285,
  kX86SysExit = 286,

  // AArch64 sync hypercalls.
  kAArch64EmulateInstruction = 0x200,
  kAArch64Breakpoint = 0x201,
};

enum StateFieldOffset : uint64_t {
  kAddrToLoad = 8,  // ArchState.addr_to_load union at offset 8
  kRAX = 2216,
  kRBX = 2232,
  kRCX = 2248,
  kRDX = 2264,
};

llvm::Value *stateFieldPtr(llvm::IRBuilder<> &B, llvm::Value *state,
                            uint64_t byte_offset) {
  return B.CreateInBoundsGEP(llvm::Type::getInt8Ty(B.getContext()), state,
                              B.getInt64(byte_offset));
}

void emitCPUID(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *eax_ptr = stateFieldPtr(B, state, kRAX);
  auto *ecx_ptr = stateFieldPtr(B, state, kRCX);
  auto *leaf = B.CreateLoad(i32_ty, eax_ptr, "cpuid.leaf");
  auto *subleaf = B.CreateLoad(i32_ty, ecx_ptr, "cpuid.subleaf");

  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty, i32_ty, i32_ty),
      {i32_ty, i32_ty}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "cpuid",
      "={eax},={ebx},={ecx},={edx},{eax},{ecx},~{dirflag},~{fpsr},~{flags}",
      true);
  auto *result = B.CreateCall(asm_ty, ia, {leaf, subleaf}, "cpuid");

  B.CreateStore(B.CreateExtractValue(result, 0), stateFieldPtr(B, state, kRAX));
  B.CreateStore(B.CreateExtractValue(result, 1), stateFieldPtr(B, state, kRBX));
  B.CreateStore(B.CreateExtractValue(result, 2), stateFieldPtr(B, state, kRCX));
  B.CreateStore(B.CreateExtractValue(result, 3), stateFieldPtr(B, state, kRDX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void emitRDTSC(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *rdtsc_fn = llvm::Intrinsic::getOrInsertDeclaration(
      CI->getModule(), llvm::Intrinsic::readcyclecounter);
  auto *tsc = B.CreateCall(rdtsc_fn, {}, "rdtsc");

  auto *lo = B.CreateTrunc(tsc, i32_ty, "rdtsc.lo");
  auto *hi = B.CreateTrunc(
      B.CreateLShr(tsc, llvm::ConstantInt::get(i64_ty, 32)),
      i32_ty, "rdtsc.hi");

  B.CreateStore(lo, stateFieldPtr(B, state, kRAX));
  B.CreateStore(hi, stateFieldPtr(B, state, kRDX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void emitRDTSCP(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty, i32_ty), {}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "rdtscp",
      "={eax},={edx},={ecx},~{dirflag},~{fpsr},~{flags}", true);
  auto *result = B.CreateCall(asm_ty, ia, {}, "rdtscp");

  B.CreateStore(B.CreateExtractValue(result, 0), stateFieldPtr(B, state, kRAX));
  B.CreateStore(B.CreateExtractValue(result, 1), stateFieldPtr(B, state, kRDX));
  B.CreateStore(B.CreateExtractValue(result, 2), stateFieldPtr(B, state, kRCX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower kAssertPrivileged / kAMD64EmulateInstruction: NOP — just erase.
void emitNopHyperCall(llvm::CallInst *CI) {
  llvm::Value *mem = CI->getArgOperand(1);
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower RDMSR: read ECX (MSR index), emit rdmsr, write EAX:EDX.
void emitRDMSR(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *ecx = B.CreateLoad(i32_ty, stateFieldPtr(B, state, kRCX), "msr.idx");

  auto *asm_ty = llvm::FunctionType::get(
      llvm::StructType::get(i32_ty, i32_ty), {i32_ty}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "rdmsr",
      "={eax},={edx},{ecx},~{dirflag},~{fpsr},~{flags}", true);
  auto *result = B.CreateCall(asm_ty, ia, {ecx}, "rdmsr");

  B.CreateStore(B.CreateExtractValue(result, 0), stateFieldPtr(B, state, kRAX));
  B.CreateStore(B.CreateExtractValue(result, 1), stateFieldPtr(B, state, kRDX));

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower WRMSR: read ECX/EAX/EDX from state, emit wrmsr.
void emitWRMSR(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *ecx = B.CreateLoad(i32_ty, stateFieldPtr(B, state, kRCX), "msr.idx");
  auto *eax = B.CreateLoad(i32_ty, stateFieldPtr(B, state, kRAX), "msr.lo");
  auto *edx = B.CreateLoad(i32_ty, stateFieldPtr(B, state, kRDX), "msr.hi");

  auto *asm_ty = llvm::FunctionType::get(void_ty, {i32_ty, i32_ty, i32_ty}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, "wrmsr",
      "{ecx},{eax},{edx},~{dirflag},~{fpsr},~{flags}", true);
  B.CreateCall(asm_ty, ia, {ecx, eax, edx});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower LGDT: read addr_to_load from state, emit lgdt.
void emitLGDT(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *addr = B.CreateLoad(i64_ty, stateFieldPtr(B, state, kAddrToLoad), "gdtr.addr");
  auto *ptr = B.CreateIntToPtr(addr, llvm::PointerType::getUnqual(Ctx));

  auto *asm_ty = llvm::FunctionType::get(void_ty, {llvm::PointerType::getUnqual(Ctx)}, false);
  auto *ia = llvm::InlineAsm::get(asm_ty, "lgdt ($0)", "r,~{memory}", true);
  B.CreateCall(asm_ty, ia, {ptr});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower LIDT: read addr_to_load from state, emit lidt.
void emitLIDT(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  auto *addr = B.CreateLoad(i64_ty, stateFieldPtr(B, state, kAddrToLoad), "idtr.addr");
  auto *ptr = B.CreateIntToPtr(addr, llvm::PointerType::getUnqual(Ctx));

  auto *asm_ty = llvm::FunctionType::get(void_ty, {llvm::PointerType::getUnqual(Ctx)}, false);
  auto *ia = llvm::InlineAsm::get(asm_ty, "lidt ($0)", "r,~{memory}", true);
  B.CreateCall(asm_ty, ia, {ptr});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower WBINVD: no-operand cache invalidate.
void emitWBINVD(llvm::CallInst *CI) {
  llvm::IRBuilder<> B(CI);
  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());
  llvm::Value *mem = CI->getArgOperand(1);

  auto *asm_ty = llvm::FunctionType::get(void_ty, {}, false);
  auto *ia = llvm::InlineAsm::get(asm_ty, "wbinvd", "~{memory}", true);
  B.CreateCall(asm_ty, ia, {});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower SYSCALL/SYSENTER/SYSEXIT: emit the raw instruction.
void emitBarePrivilegedInsn(llvm::CallInst *CI, const char *mnemonic) {
  llvm::IRBuilder<> B(CI);
  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());
  llvm::Value *mem = CI->getArgOperand(1);

  auto *asm_ty = llvm::FunctionType::get(void_ty, {}, false);
  auto *ia = llvm::InlineAsm::get(
      asm_ty, mnemonic,
      "~{rcx},~{r11},~{memory},~{dirflag},~{fpsr},~{flags}", true);
  B.CreateCall(asm_ty, ia, {});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

/// Lower MOV CRn: emit mov to control register inline asm.
/// The source value is already stored to the destination by remill semantics;
/// we read the written value from state and emit the actual mov crN, reg.
void emitWriteControlReg(llvm::CallInst *CI, unsigned cr_num) {
  llvm::IRBuilder<> B(CI);
  auto &Ctx = CI->getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);

  // The source register value was already written to the destination by
  // WRITE_CONTROL_REG semantics.  We use RAX as the transfer register.
  auto *val = B.CreateLoad(i64_ty, stateFieldPtr(B, state, kRAX), "cr.val");

  std::string asm_str = "mov %cr" + std::to_string(cr_num) + ", $0";
  auto *asm_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);
  auto *ia = llvm::InlineAsm::get(asm_ty, asm_str, "r,~{memory}", true);
  B.CreateCall(asm_ty, ia, {val});

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}
void emitGenericSyncStub(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();

  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(1);
  llvm::Value *hyper_call_id = CI->getArgOperand(2);

  auto *void_ty = llvm::Type::getVoidTy(CI->getContext());
  auto *i32_ty = llvm::Type::getInt32Ty(CI->getContext());
  auto *FT = llvm::FunctionType::get(void_ty, {state->getType(), i32_ty}, false);
  auto callee = getOrDeclareHelper(M, "__omill_sync_hyper_call", FT);

  Builder.CreateCall(callee, {state, hyper_call_id});
  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();
}

void lowerSyncHyperCall(llvm::CallInst *CI) {
  auto *id = CI->getArgOperand(2);
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(id);
  if (!ci) {
    emitGenericSyncStub(CI);
    return;
  }

  switch (ci->getZExtValue()) {
    case kAssertPrivileged:
    case kX86EmulateInstruction:
    case kAMD64EmulateInstruction:
    // Segment register writes: value already written to State by semantics.
    // In x86-64 long mode, ES/DS/SS selectors are ignored.  FS/GS selector
    // loads are not meaningful without a matching MSR write.  Emit NOP.
    case kX86SetSegmentES:
    case kX86SetSegmentSS:
    case kX86SetSegmentDS:
    case kX86SetSegmentFS:
    case kX86SetSegmentGS:
    // Debug register writes: value already written to State by semantics.
    // DR0-DR7 are CPU hardware debug state; emit NOP for recompilation.
    case kX86SetDebugReg:
    case kAMD64SetDebugReg:
    // Control register writes (x86 variants): same treatment as AMD64 CRs.
    case kX86SetControlReg0:
    case kX86SetControlReg1:
    case kX86SetControlReg2:
    case kX86SetControlReg3:
    case kX86SetControlReg4:
      emitNopHyperCall(CI);
      break;
    case kX86CPUID:
      emitCPUID(CI);
      break;
    case kX86ReadTSC:
      emitRDTSC(CI);
      break;
    case kX86ReadTSCP:
      emitRDTSCP(CI);
      break;
    case kX86ReadModelSpecificRegister:
      emitRDMSR(CI);
      break;
    case kX86WriteModelSpecificRegister:
      emitWRMSR(CI);
      break;
    case kX86LoadGlobalDescriptorTable:
      emitLGDT(CI);
      break;
    case kX86LoadInterruptDescriptorTable:
      emitLIDT(CI);
      break;
    case kX86WriteBackInvalidate:
      emitWBINVD(CI);
      break;
    case kAMD64SetControlReg0:
      emitWriteControlReg(CI, 0);
      break;
    case kAMD64SetControlReg1:
      emitWriteControlReg(CI, 1);
      break;
    case kAMD64SetControlReg2:
      emitWriteControlReg(CI, 2);
      break;
    case kAMD64SetControlReg3:
      emitWriteControlReg(CI, 3);
      break;
    case kAMD64SetControlReg4:
      emitWriteControlReg(CI, 4);
      break;
    case kAMD64SetControlReg8:
      emitWriteControlReg(CI, 8);
      break;
    case kX86SysCall:
      emitBarePrivilegedInsn(CI, "syscall");
      break;
    case kX86SysEnter:
      emitBarePrivilegedInsn(CI, "sysenter");
      break;
    case kX86SysExit:
      emitBarePrivilegedInsn(CI, "sysexit");
      break;
    // AArch64: emulate instruction and breakpoint are NOP for recompilation.
    case kAArch64EmulateInstruction:
    case kAArch64Breakpoint:
      emitNopHyperCall(CI);
      break;
    default:
      emitGenericSyncStub(CI);
      break;
  }
}

void lowerAsyncHyperCall(llvm::CallInst *CI) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  llvm::Value *state = CI->getArgOperand(0);
  llvm::Value *mem = CI->getArgOperand(2);

  // Remill stores AsyncHyperCall::Name at State+0 (i32) and the interrupt
  // vector at State+8 (i32/i64) immediately before this call.  Walk backward
  // to find the constant values so we can emit the right native instruction.
  //
  // The scan uses offset-based resolution (not raw pointer equality) to
  // handle GEP chains that SROA or InstCombine may introduce.  It also
  // crosses single-predecessor block boundaries, since SimplifyCFG or
  // inlining can move the store to a predecessor.
  uint32_t hyper_call_code = 0;  // AsyncHyperCall::Name enum
  uint32_t vector = 0;

  auto &DL = CI->getModule()->getDataLayout();

  // Resolve a pointer to its byte offset from the State argument.
  auto resolveStateOff = [&](llvm::Value *ptr) -> int64_t {
    int64_t total = 0;
    llvm::Value *base = ptr;
    while (true) {
      if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
        llvm::APInt ap(64, 0);
        if (GEP->accumulateConstantOffset(DL, ap)) {
          total += ap.getSExtValue();
          base = GEP->getPointerOperand();
          continue;
        }
        return -1;
      }
      if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
        base = BC->getOperand(0);
        continue;
      }
      break;
    }
    return (base == state && total >= 0) ? total : -1;
  };

  auto *scan_bb = CI->getParent();
  auto scan_end = CI->getIterator();
  for (unsigned depth = 0; depth < 4; ++depth) {
    for (auto It = scan_end; It != scan_bb->begin();) {
      --It;
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*It);
      if (!SI) continue;
      int64_t off = resolveStateOff(SI->getPointerOperand());
      if (off == 0 && !hyper_call_code) {
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand()))
          hyper_call_code = static_cast<uint32_t>(C->getZExtValue());
      } else if (off == 8 && !vector) {
        if (auto *C = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand()))
          vector = static_cast<uint32_t>(C->getZExtValue());
      }
      if (hyper_call_code && vector) break;
    }
    if (hyper_call_code && vector) break;
    auto *pred = scan_bb->getSinglePredecessor();
    if (!pred || pred == scan_bb) break;
    scan_bb = pred;
    scan_end = scan_bb->end();
  }

  // Metadata fallback: if the backward scan didn't find a constant store
  // (e.g., PromoteStateToSSA promoted State.hyper_call to an alloca that
  // ADCE later removed), recover the hyper call code from the metadata
  // that the block lifter attached.
  if (!hyper_call_code) {
    if (auto *md = CI->getMetadata("omill.hyper_call_fn")) {
      if (auto *str = llvm::dyn_cast<llvm::MDString>(md->getOperand(0))) {
        auto fn = str->getString();
        // Map ISEL function names to AsyncHyperCall::Name values.
        if (fn.starts_with("INT1"))
          hyper_call_code = 1;  // kX86Int1
        else if (fn.starts_with("INT3"))
          hyper_call_code = 2;  // kX86Int3
        else if (fn.starts_with("INTO"))
          hyper_call_code = 3;  // kX86IntO
        else if (fn.starts_with("INT_"))
          hyper_call_code = 4;  // kX86IntN
        else if (fn.starts_with("BOUND"))
          hyper_call_code = 5;  // kX86Bound
        else if (fn.starts_with("IRET"))
          hyper_call_code = 6;  // kX86IRet
        else if (fn.starts_with("SYSCALL"))
          hyper_call_code = 7;  // kX86SysCall
        else if (fn.starts_with("SYSRET"))
          hyper_call_code = 8;  // kX86SysRet
        else if (fn.starts_with("SYSENTER"))
          hyper_call_code = 9;  // kX86SysEnter
        else if (fn.starts_with("SYSEXIT"))
          hyper_call_code = 10; // kX86SysExit
        else if (fn.starts_with("JMP_FAR") || fn.starts_with("CALL_FAR"))
          hyper_call_code = 11; // kX86JmpFar
        if (std::getenv("OMILL_DEBUG_HYPER_CALL"))
          llvm::errs() << "[hyper] recovered code=" << hyper_call_code
                       << " from metadata fn=" << fn << "\n";
      }
    }
  }

  // Emit the appropriate native instruction via inline asm.
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *void_fn_ty = llvm::FunctionType::get(void_ty, false);

  // AsyncHyperCall::Name values from remill/Arch/Runtime/HyperCall.h:
  //   kInvalid=0, kX86Int1=1, kX86Int3=2, kX86IntO=3, kX86IntN=4,
  //   kX86Bound=5, kX86IRet=6, kX86SysCall=7, ...
  bool is_noreturn = false;
  auto *call_bb = CI->getParent();
  switch (hyper_call_code) {
    case 2: {  // kX86Int3 — debug breakpoint, returns to next instruction
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "int3", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      break;
    }
    case 4: {  // kX86IntN — software interrupt (e.g. int 0x29 = __fastfail)
      std::string asm_str = "int $$" + std::to_string(vector);
      auto *IA = llvm::InlineAsm::get(void_fn_ty, asm_str, "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = (vector == 0x29);
      break;
    }
    case 1: {  // kX86Int1 — software interrupt 1
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "int $$1", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      break;
    }
    case 3: {  // kX86IntO (into — overflow interrupt)
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "into", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      break;
    }
    case 5: {  // kX86Bound — invalid in 64-bit long mode
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "ud2", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    case 6: {  // kX86IRet — interrupt return
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "iretq", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    case 7: {  // kX86SysCall — transition to kernel
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "syscall", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    case 8: {  // kX86SysRet — return from syscall to user mode
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "sysretq", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    case 9: {  // kX86SysEnter — fast system call entry
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "sysenter", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    case 10: {  // kX86SysExit — return from sysenter
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "sysexit", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    case 11: {  // kX86JmpFar — far jump/call in x64 long mode.
      // The semantic already wrote the target offset to REG_PC and the
      // segment selector to REG_CS.flat.  In long mode the segment base
      // is forced to 0, so the far transfer is just an indirect
      // jump/call to the offset — which the normal dispatch flow
      // handles.  Emit NOP; the hyper call is effectively a no-op.
      CI->replaceAllUsesWith(mem);
      CI->eraseFromParent();
      return;  // CI erased, skip the common tail below.
    }
    case 12: {  // kAArch64SupervisorCall — SVC #imm
      std::string asm_str = "svc #" + std::to_string(vector);
      auto *IA = llvm::InlineAsm::get(void_fn_ty, asm_str, "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      is_noreturn = true;
      break;
    }
    default: {
      // Unknown async hyper call — emit ud2 (x86) or brk (AArch64).
      if (std::getenv("OMILL_DEBUG_HYPER_CALL")) {
        llvm::errs() << "[hyper] unresolved async hyper_call_code="
                     << hyper_call_code << " in "
                     << CI->getParent()->getParent()->getName()
                     << " bb=" << CI->getParent()->getName() << "\n";
        // Dump preceding stores for debugging.
        auto *dbb = CI->getParent();
        for (auto dit = CI->getReverseIterator();
             dit != dbb->rend(); ++dit) {
          if (auto *dsi = llvm::dyn_cast<llvm::StoreInst>(&*dit)) {
            int64_t doff = resolveStateOff(dsi->getPointerOperand());
            llvm::errs() << "[hyper]   store off=" << doff << " val=";
            dsi->getValueOperand()->printAsOperand(llvm::errs(), false);
            llvm::errs() << " ptr=";
            dsi->getPointerOperand()->printAsOperand(llvm::errs(), false);
            llvm::errs() << " (state=";
            state->printAsOperand(llvm::errs(), false);
            llvm::errs() << ")\n";
          }
        }
      }
      auto *IA = llvm::InlineAsm::get(void_fn_ty, "ud2", "",
                                      /*hasSideEffects=*/true);
      Builder.CreateCall(IA);
      break;
    }
  }

  CI->replaceAllUsesWith(mem);
  CI->eraseFromParent();

  if (is_noreturn) {
    // __fastfail is noreturn — kernel terminates the process.
    if (auto *Term = call_bb->getTerminator())
      Term->eraseFromParent();
    llvm::IRBuilder<> B(call_bb);
    B.CreateUnreachable();
  }
}

void lowerIOPort(llvm::CallInst *CI, IntrinsicKind kind) {
  llvm::IRBuilder<> Builder(CI);
  auto &Ctx = CI->getContext();

  bool is_read = (kind == IntrinsicKind::kReadIOPort8 ||
                  kind == IntrinsicKind::kReadIOPort16 ||
                  kind == IntrinsicKind::kReadIOPort32);

  unsigned bit_width;
  switch (kind) {
    case IntrinsicKind::kReadIOPort8:
    case IntrinsicKind::kWriteIOPort8:
      bit_width = 8;
      break;
    case IntrinsicKind::kReadIOPort16:
    case IntrinsicKind::kWriteIOPort16:
      bit_width = 16;
      break;
    default:
      bit_width = 32;
      break;
  }

  auto *int_ty = llvm::IntegerType::get(Ctx, bit_width);
  auto *i16_ty = llvm::Type::getInt16Ty(Ctx);

  // Truncate the 64-bit port address to i16 (x86 I/O port space is 16-bit).
  auto *port = Builder.CreateTrunc(CI->getArgOperand(1), i16_ty);

  if (is_read) {
    // AT&T syntax: inb/inw/inl $port, $result
    const char *asm_str = (bit_width == 8)  ? "inb $1, $0" :
                          (bit_width == 16) ? "inw $1, $0" :
                                              "inl $1, $0";
    auto *asm_ty = llvm::FunctionType::get(int_ty, {i16_ty}, false);
    auto *ia = llvm::InlineAsm::get(asm_ty, asm_str,
                                    "={ax},{dx},~{dirflag},~{fpsr},~{flags}",
                                    /*hasSideEffects=*/true);
    auto *result = Builder.CreateCall(ia, {port});
    CI->replaceAllUsesWith(result);
  } else {
    // AT&T syntax: outb/outw/outl $value, $port
    const char *asm_str = (bit_width == 8)  ? "outb $1, $0" :
                          (bit_width == 16) ? "outw $1, $0" :
                                              "outl $1, $0";
    auto *val = CI->getArgOperand(2);
    auto *void_ty = llvm::Type::getVoidTy(Ctx);
    auto *asm_ty = llvm::FunctionType::get(void_ty, {i16_ty, int_ty}, false);
    auto *ia = llvm::InlineAsm::get(asm_ty, asm_str,
                                    "{dx},{ax},~{dirflag},~{fpsr},~{flags}",
                                    /*hasSideEffects=*/true);
    Builder.CreateCall(ia, {port, val});
    // Write intrinsic returns Memory* — replace with input Memory* (arg 0).
    CI->replaceAllUsesWith(CI->getArgOperand(0));
  }
  CI->eraseFromParent();
}

void lowerFPUOp(llvm::CallInst *CI, IntrinsicKind kind) {
  llvm::IRBuilder<> Builder(CI);
  auto &M = *CI->getModule();
  auto &Ctx = CI->getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *except_state = getOrCreateFEnvI32Global(M, "__omill_fenv_except_state");
  auto *rounding_state =
      getOrCreateFEnvI32Global(M, "__omill_fenv_rounding_mode");

  switch (kind) {
    case IntrinsicKind::kFPUExceptionTest: {
      auto *state = Builder.CreateLoad(i32_ty, except_state, "fenv.excepts");
      auto *mask = CI->getArgOperand(0);
      auto *result = Builder.CreateAnd(state, mask, "fenv.test");
      CI->replaceAllUsesWith(result);
      break;
    }
    case IntrinsicKind::kFPUExceptionClear: {
      auto *state = Builder.CreateLoad(i32_ty, except_state, "fenv.excepts");
      auto *mask = CI->getArgOperand(0);
      auto *cleared = Builder.CreateAnd(state, Builder.CreateNot(mask),
                                        "fenv.cleared");
      Builder.CreateStore(cleared, except_state);
      if (!CI->getType()->isVoidTy())
        CI->replaceAllUsesWith(llvm::ConstantInt::get(i32_ty, 0));
      break;
    }
    case IntrinsicKind::kFPUExceptionRaise: {
      auto *state = Builder.CreateLoad(i32_ty, except_state, "fenv.excepts");
      auto *raised =
          Builder.CreateOr(state, CI->getArgOperand(0), "fenv.raised");
      Builder.CreateStore(raised, except_state);
      if (!CI->getType()->isVoidTy())
        CI->replaceAllUsesWith(llvm::ConstantInt::get(i32_ty, 0));
      break;
    }
    case IntrinsicKind::kFPUSetRounding: {
      Builder.CreateStore(CI->getArgOperand(0), rounding_state);
      if (!CI->getType()->isVoidTy())
        CI->replaceAllUsesWith(llvm::ConstantInt::get(i32_ty, 0));
      break;
    }
    case IntrinsicKind::kFPUGetRounding: {
      auto *result =
          Builder.CreateLoad(i32_ty, rounding_state, "fenv.rounding");
      CI->replaceAllUsesWith(result);
      break;
    }
    default:
      return;
  }
  CI->eraseFromParent();
}

bool lowerFP80NearbyIntIntrinsics(llvm::Function &F) {
  llvm::SmallVector<llvm::CallInst *, 8> to_lower;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (CI && isNearbyIntFP80Intrinsic(CI))
        to_lower.push_back(CI);
    }
  }

  if (to_lower.empty())
    return false;

  for (auto *CI : to_lower) {
    llvm::IRBuilder<> Builder(CI);
    auto *result = createFP80RoundToIntegral(Builder, CI->getArgOperand(0));
    CI->replaceAllUsesWith(result);
    CI->eraseFromParent();
  }
  return true;
}

void lowerX86Specific(llvm::CallInst *CI) {
  CI->replaceAllUsesWith(CI->getArgOperand(0));
  CI->eraseFromParent();
}

bool lowerHyperCalls(llvm::Function &F, IntrinsicTable &table) {
  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  llvm::SmallVector<PendingCall, 16> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        auto cat = IntrinsicTable::categoryOf(kind);
        if (cat == IntrinsicCategory::kHyperCall ||
            cat == IntrinsicCategory::kIOPort ||
            cat == IntrinsicCategory::kFPU ||
            cat == IntrinsicCategory::kX86Specific)
          pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  for (auto &[CI, kind] : pending) {
    auto cat = IntrinsicTable::categoryOf(kind);
    switch (cat) {
      case IntrinsicCategory::kHyperCall:
        if (kind == IntrinsicKind::kSyncHyperCall)
          lowerSyncHyperCall(CI);
        else
          lowerAsyncHyperCall(CI);
        break;
      case IntrinsicCategory::kIOPort:
        lowerIOPort(CI, kind);
        break;
      case IntrinsicCategory::kFPU:
        lowerFPUOp(CI, kind);
        break;
      case IntrinsicCategory::kX86Specific:
        lowerX86Specific(CI);
        break;
      default:
        break;
    }
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 6: ErrorMissing — lower error/missing block handlers
// ===----------------------------------------------------------------------===

bool lowerErrorAndMissing(llvm::Function &F, IntrinsicTable &table) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  struct PendingCall {
    llvm::CallInst *CI;
    IntrinsicKind kind;
  };
  // Only collect the FIRST error/missing call per block.  After semantic
  // inlining, a block may contain multiple such calls.  Processing the first
  // one inserts a `ret` and erases everything after it, so later calls in
  // the same block would become dangling pointers.
  llvm::DenseSet<llvm::BasicBlock *> seen_blocks;
  llvm::SmallVector<PendingCall, 4> pending;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I)) {
        auto kind = table.classifyCall(CI);
        if (kind == IntrinsicKind::kError ||
            kind == IntrinsicKind::kMissingBlock)
          if (seen_blocks.insert(&BB).second)
            pending.push_back({CI, kind});
      }

  if (pending.empty())
    return false;

  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *handler_ty = llvm::FunctionType::get(void_ty, {i64_ty}, false);

  auto error_handler =
      M.getOrInsertFunction("__omill_error_handler", handler_ty);
  auto missing_handler =
      M.getOrInsertFunction("__omill_missing_block_handler", handler_ty);

  for (auto &[CI, kind] : pending) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Value *pc = CI->getArgOperand(1);
    llvm::CallInst *replacement_call = nullptr;
    if (kind == IntrinsicKind::kError)
      replacement_call = Builder.CreateCall(error_handler, {pc});
    else
      replacement_call = Builder.CreateCall(missing_handler, {pc});
    replacement_call->copyMetadata(*CI);

    // Return the incoming memory token (arg 2) rather than poison so
    // that callers who inline this function observe a clean return
    // instead of propagating poison through the memory-threading chain.
    // Poison would cause LLVM to eliminate the entire call subtree as
    // undefined, collapsing exit handlers to `body: unreachable`.
    llvm::Instruction *new_term;
    if (F.getReturnType()->isVoidTy())
      new_term = Builder.CreateRetVoid();
    else
      new_term = Builder.CreateRet(CI->getArgOperand(2));

    CI->replaceAllUsesWith(CI->getArgOperand(2));
    CI->eraseFromParent();

    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 7: Return — lower __remill_function_return to ret
// ===----------------------------------------------------------------------===

bool lowerFunctionReturn(llvm::Function &F, IntrinsicTable &table) {
  // Only collect the FIRST __remill_function_return per block.
  // After semantic inlining, a block may contain multiple return intrinsics
  // from different inlined callees.  Processing the first one inserts a `ret`
  // and erases everything after it (including subsequent return calls), so
  // keeping later calls in the worklist would leave dangling pointers.
  llvm::DenseSet<llvm::BasicBlock *> seen_blocks;
  llvm::SmallVector<llvm::CallInst *, 4> return_calls;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (table.classifyCall(CI) == IntrinsicKind::kFunctionReturn)
          if (seen_blocks.insert(&BB).second)
            return_calls.push_back(CI);

  if (return_calls.empty())
    return false;

  for (auto *CI : return_calls) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Instruction *new_term;
    if (F.getReturnType()->isVoidTy())
      new_term = Builder.CreateRetVoid();
    else
      new_term = Builder.CreateRet(CI->getArgOperand(2));

    // Preserve the threaded Memory* token instead of introducing poison.
    // Some lifted traces still feed this value into fallback dispatch paths.
    CI->replaceAllUsesWith(CI->getArgOperand(2));
    CI->eraseFromParent();

    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 8: Call — lower __remill_function_call
// ===----------------------------------------------------------------------===

bool lowerFunctionCall(llvm::Function &F, IntrinsicTable &table,
                       const LiftedFunctionMap *lifted) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  llvm::SmallVector<llvm::CallInst *, 8> call_intrinsics;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (table.classifyCall(CI) == IntrinsicKind::kFunctionCall)
          call_intrinsics.push_back(CI);

  if (call_intrinsics.empty())
    return false;

  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty = llvm::FunctionType::get(
      mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);

  for (auto *CI : call_intrinsics) {
    llvm::IRBuilder<> Builder(CI);
    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::Value *result = nullptr;

    if (auto *const_pc = llvm::dyn_cast<llvm::ConstantInt>(target_pc)) {
      auto *target_fn = lifted ? lifted->lookup(const_pc->getZExtValue())
                               : nullptr;
      if (!target_fn)
        target_fn = findLiftedOrBlockFunctionByPC(
            M, const_pc->getZExtValue());
      if (target_fn)
        result = Builder.CreateCall(target_fn, {state, target_pc, mem});
    }

    if (!result) {
      auto dispatcher = M.getOrInsertFunction(
          canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kCall, M),
          lifted_fn_ty);
      result = Builder.CreateCall(dispatcher, {state, target_pc, mem});
    }

    CI->replaceAllUsesWith(result);
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 9: Jump — lower __remill_jump
// ===----------------------------------------------------------------------===

bool lowerJump(llvm::Function &F, IntrinsicTable &table,
               const LiftedFunctionMap *lifted) {
  auto &M = *F.getParent();
  auto &Ctx = F.getContext();

  // Only collect the FIRST __remill_jump per block — same rationale as
  // lowerFunctionReturn: processing the first inserts a terminator and
  // erases everything after it, invalidating later calls in the same block.
  llvm::DenseSet<llvm::BasicBlock *> seen_blocks;
  llvm::SmallVector<llvm::CallInst *, 8> jump_calls;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (table.classifyCall(CI) == IntrinsicKind::kJump)
          if (seen_blocks.insert(&BB).second)
            jump_calls.push_back(CI);

  if (jump_calls.empty())
    return false;

  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty = llvm::FunctionType::get(
      mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);

  llvm::DenseMap<uint64_t, llvm::BasicBlock *> inferred_pc_map;
  bool inferred_pc_map_built = false;

  for (auto *CI : jump_calls) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *target_pc = CI->getArgOperand(1);
    llvm::Value *mem = CI->getArgOperand(2);

    llvm::Instruction *new_term = nullptr;

    if (auto *const_pc = llvm::dyn_cast<llvm::ConstantInt>(target_pc)) {
      uint64_t pc_val = const_pc->getZExtValue();

      if (auto *target_bb = findBlockForPC(F, pc_val))
        new_term = Builder.CreateBr(target_bb);

      if (!new_term) {
        auto *target_fn = lifted ? lifted->lookup(pc_val) : nullptr;
        if (!target_fn)
          target_fn = findLiftedOrBlockFunctionByPC(M, pc_val);
        if (target_fn) {
          auto *tail_call =
              Builder.CreateCall(target_fn, {state, target_pc, mem});
          tail_call->setTailCallKind(llvm::CallInst::TCK_MustTail);
          new_term = Builder.CreateRet(tail_call);
        }
      }
    }

    if (!new_term) {
      // Fallback br selector: dispatch via the configured unresolved jump
      // intrinsic.
      // Note: InlineJumpTargetsPass lowers most __remill_jump calls early
      // (before state optimization) with proper PC→block switches.
      // This path handles any remaining jumps that weren't lowered early.
      auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
      llvm::SmallVector<std::pair<uint64_t, llvm::BasicBlock *>, 32> block_pcs;
      for (auto &TargetBB : F) {
        uint64_t pc = extractBlockPC(TargetBB.getName());
        if (pc != 0)
          block_pcs.push_back({pc, &TargetBB});
      }

      // If block_<pc> names were stripped, infer a small set of candidate
      // targets from this specific jump value.
      if (block_pcs.empty()) {
        if (!inferred_pc_map_built) {
          inferred_pc_map = collectBlockPCMap(F);
          inferred_pc_map_built = true;
        }
        llvm::DenseSet<uint64_t> seen_pcs;
        auto candidate_pcs = collectPossiblePCValues(target_pc, F, 32);
        if (debugJumpSelector()) {
          llvm::errs() << "[LowerJump] " << F.getName()
                       << " inferred candidates=" << candidate_pcs.size()
                       << " inferred_map=" << inferred_pc_map.size() << "\n";
        }
        for (uint64_t pc : candidate_pcs) {
          if (!seen_pcs.insert(pc).second)
            continue;
          if (auto it = inferred_pc_map.find(pc); it != inferred_pc_map.end())
            block_pcs.push_back({pc, it->second});
        }
      }
      if (debugJumpSelector() && block_pcs.empty()) {
        llvm::errs() << "[LowerJump] " << F.getName()
                     << " produced empty selector; keeping dispatch fallback\n";
      }

      auto *fallback_bb = llvm::BasicBlock::Create(
          Ctx, "jump_dispatch_fallback", &F);
      {
        llvm::IRBuilder<> FBBuilder(fallback_bb);
        auto dispatcher = M.getOrInsertFunction(
            canonicalDispatchIntrinsicName(DispatchIntrinsicKind::kJump, M),
            lifted_fn_ty);
        auto *result =
            FBBuilder.CreateCall(dispatcher, {state, target_pc, mem});
        FBBuilder.CreateRet(result);
      }

      auto *sw = Builder.CreateSwitch(target_pc, fallback_bb,
                                      block_pcs.size());
      for (auto [pc, target_bb] : block_pcs)
        sw->addCase(llvm::ConstantInt::get(i64_ty, pc), target_bb);
      new_term = sw;
    }

    // Preserve the threaded Memory* token instead of introducing poison.
    // Some lifted traces still feed this value into fallback dispatch paths.
    CI->replaceAllUsesWith(mem);
    CI->eraseFromParent();

    while (&BB->back() != new_term) {
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
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 10: Undefined — replace with freeze(poison)
// ===----------------------------------------------------------------------===

bool lowerUndefinedIntrinsics(llvm::Function &F, IntrinsicTable &table) {
  llvm::SmallVector<llvm::CallInst *, 16> to_lower;

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *CI = llvm::dyn_cast<llvm::CallInst>(&I))
        if (IntrinsicTable::categoryOf(table.classifyCall(CI)) ==
            IntrinsicCategory::kUndefined)
          to_lower.push_back(CI);

  if (to_lower.empty())
    return false;

  for (auto *CI : to_lower) {
    llvm::IRBuilder<> Builder(CI);
    auto *frozen = Builder.CreateFreeze(llvm::PoisonValue::get(CI->getType()));
    CI->replaceAllUsesWith(frozen);
    CI->eraseFromParent();
  }
  return true;
}

// ===----------------------------------------------------------------------===
// Category 11: ResolvedDispatch — lower dispatch_call(ptrtoint(@import))
//   to native Win64 calls
// ===----------------------------------------------------------------------===

static constexpr uint64_t kRCXOffset = 2248;
static constexpr uint64_t kRDXOffset = 2264;
static constexpr uint64_t kR8Offset = 2344;
static constexpr uint64_t kR9Offset = 2360;
static constexpr uint64_t kRAXOffset = 2216;

llvm::Value *buildStateLoad(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                            uint64_t offset, const llvm::Twine &name) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  return Builder.CreateLoad(Builder.getInt64Ty(), gep, name);
}

void buildStateStore(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                     uint64_t offset, llvm::Value *val) {
  auto *gep = Builder.CreateGEP(Builder.getInt8Ty(), state_ptr,
                                Builder.getInt64(offset));
  Builder.CreateStore(val, gep);
}

bool lowerResolvedDispatchCalls(llvm::Function &F) {
  if (F.arg_size() == 0)
    return false;

  llvm::SmallVector<llvm::CallInst *, 4> to_lower;

  for (auto &BB : F)
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isDispatchCallName(callee->getName()))
        continue;
      if (call->arg_size() < 3)
        continue;

      auto *ptoi =
          llvm::dyn_cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
      if (!ptoi)
        continue;
      auto *target_fn =
          llvm::dyn_cast<llvm::Function>(ptoi->getPointerOperand());
      if (!target_fn)
        continue;
      if (target_fn->getDLLStorageClass() !=
          llvm::GlobalValue::DLLImportStorageClass)
        continue;

      to_lower.push_back(call);
    }

  if (to_lower.empty())
    return false;

  auto &Ctx = F.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *native_ft = llvm::FunctionType::get(
      i64_ty, {i64_ty, i64_ty, i64_ty, i64_ty}, false);

  for (auto *call : to_lower) {
    auto *ptoi =
        llvm::cast<llvm::PtrToIntOperator>(call->getArgOperand(1));
    auto *target_fn =
        llvm::cast<llvm::Function>(ptoi->getPointerOperand());
    auto *state_ptr = call->getArgOperand(0);

    llvm::IRBuilder<> Builder(call);

    auto *rcx = buildStateLoad(Builder, state_ptr, kRCXOffset, "rcx");
    auto *rdx = buildStateLoad(Builder, state_ptr, kRDXOffset, "rdx");
    auto *r8 = buildStateLoad(Builder, state_ptr, kR8Offset, "r8");
    auto *r9 = buildStateLoad(Builder, state_ptr, kR9Offset, "r9");

    auto *result = Builder.CreateCall(
        native_ft, target_fn, {rcx, rdx, r8, r9},
        target_fn->getName().str() + ".result");

    buildStateStore(Builder, state_ptr, kRAXOffset, result);

    // The dispatch_call returned the memory token (ptr).  After
    // rewriting to a native Win64 ABI call (which returns i64 in
    // RAX), the memory token is unchanged — thread the incoming
    // memory argument through so downstream blocks don't receive
    // poison and collapse to `body: unreachable`.
    call->replaceAllUsesWith(call->getArgOperand(2));
    call->eraseFromParent();
  }
  return true;
}

}  // namespace

// ===----------------------------------------------------------------------===
// Main pass entry point
// ===----------------------------------------------------------------------===

llvm::PreservedAnalyses LowerRemillIntrinsicsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  IntrinsicTable table(*F.getParent());
  bool changed = false;

  // Fetch LiftedFunctionAnalysis lazily (only for Call/Jump categories).
  const LiftedFunctionMap *lifted = nullptr;
  if (categories_ & (LowerCategories::Call | LowerCategories::Jump)) {
    auto &MAMProxy =
        AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
    lifted =
        MAMProxy.getCachedResult<LiftedFunctionAnalysis>(*F.getParent());
  }

  // Process in correct order matching pipeline semantics.
  if (categories_ & LowerCategories::Flags)
    changed |= lowerFlagIntrinsics(F, table);
  if (categories_ & LowerCategories::Barriers)
    changed |= removeBarriers(F, table);
  if (categories_ & LowerCategories::Memory)
    changed |= lowerMemoryIntrinsics(F, table);
  if (categories_ & LowerCategories::Atomics)
    changed |= lowerAtomicIntrinsics(F, table);
  if (categories_ & LowerCategories::HyperCalls)
    changed |= lowerHyperCalls(F, table);
  if (categories_ & LowerCategories::HyperCalls)
    changed |= lowerFP80NearbyIntIntrinsics(F);
  if (categories_ & LowerCategories::ErrorMissing)
    changed |= lowerErrorAndMissing(F, table);
  if (categories_ & LowerCategories::Return)
    changed |= lowerFunctionReturn(F, table);
  if (categories_ & LowerCategories::Call)
    changed |= lowerFunctionCall(F, table, lifted);
  if (categories_ & LowerCategories::Jump)
    changed |= lowerJump(F, table, lifted);
  if (categories_ & LowerCategories::Undefined)
    changed |= lowerUndefinedIntrinsics(F, table);
  if (categories_ & LowerCategories::ResolvedDispatch)
    changed |= lowerResolvedDispatchCalls(F);

  // After memory intrinsics are lowered, the Memory* pointer (arg2) has no
  // semantic meaning.  Replace remaining uses with poison so downstream
  // passes see a clean function signature.
  if ((categories_ & LowerCategories::Memory) && F.arg_size() >= 3) {
    auto *mem_arg = F.getArg(2);
    if (!mem_arg->use_empty()) {
      mem_arg->replaceAllUsesWith(llvm::PoisonValue::get(mem_arg->getType()));
      changed = true;
    }
  }

  eraseUnusedLoweringHelperDeclarations(*F.getParent());

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
