#include "omill/Passes/ResolveForcedExceptions.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/ExceptionInfo.h"
#include "omill/Analysis/LiftedFunctionMap.h"
#include "omill/Utils/IntrinsicTable.h"
#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

// State struct offsets for x86-64 GPRs (remill).
struct RegMapping {
  unsigned state_offset;   // Byte offset in State struct
  unsigned context_offset; // Byte offset in CONTEXT struct
};

// clang-format off
static constexpr RegMapping kGPRMappings[] = {
    {2216, 0x78},  // RAX
    {2248, 0x80},  // RCX
    {2264, 0x88},  // RDX
    {2232, 0x90},  // RBX
    {2312, 0x98},  // RSP
    {2328, 0xA0},  // RBP
    {2280, 0xA8},  // RSI
    {2296, 0xB0},  // RDI
    {2344, 0xB8},  // R8
    {2360, 0xC0},  // R9
    {2376, 0xC8},  // R10
    {2392, 0xD0},  // R11
    {2408, 0xD8},  // R12
    {2424, 0xE0},  // R13
    {2440, 0xE8},  // R14
    {2456, 0xF0},  // R15
};
// clang-format on

// CONTEXT.Rip offset.
static constexpr unsigned kContextRipOffset = 0xF8;

// CONTEXT size and alignment.
static constexpr unsigned kContextSize = 1232;
static constexpr unsigned kContextAlign = 16;

// EXCEPTION_RECORD size and alignment.
static constexpr unsigned kExceptionRecordSize = 152;
static constexpr unsigned kExceptionRecordAlign = 8;

// EXCEPTION_RECORD field offsets.
static constexpr unsigned kExRecCodeOffset = 0;
static constexpr unsigned kExRecAddressOffset = 16;

// STATUS_ILLEGAL_INSTRUCTION.
static constexpr uint32_t kStatusIllegalInstruction = 0xC000001D;

// XMM register count.
static constexpr unsigned kXMMCount = 16;

// State offset for XMM[n]: 16 + n * 64 (lower 128 bits of VectorReg).
static unsigned xmmStateOffset(unsigned n) { return 16 + n * 64; }

// CONTEXT offset for XMM[n]: 0x1A0 + n * 16.
static unsigned xmmContextOffset(unsigned n) { return 0x1A0 + n * 16; }

// State offsets for handler arg registers (Win64 ABI).
static constexpr unsigned kStateRCX = 2248;
static constexpr unsigned kStateRDX = 2264;
static constexpr unsigned kStateR8 = 2344;
static constexpr unsigned kStateR9 = 2360;

/// Create a GEP to byte offset within an alloca/pointer.
static llvm::Value *gepByteOffset(llvm::IRBuilder<> &Builder,
                                  llvm::Value *base, unsigned offset) {
  auto *i8_ty = llvm::Type::getInt8Ty(Builder.getContext());
  return Builder.CreateGEP(i8_ty, base,
                           Builder.getInt32(offset));
}

/// Load an i64 from State at a given byte offset.
static llvm::Value *loadStateI64(llvm::IRBuilder<> &Builder,
                                 llvm::Value *state, unsigned offset) {
  auto *i64_ty = llvm::Type::getInt64Ty(Builder.getContext());
  auto *ptr = gepByteOffset(Builder, state, offset);
  return Builder.CreateLoad(i64_ty, ptr);
}

/// Store an i64 to State at a given byte offset.
static void storeStateI64(llvm::IRBuilder<> &Builder, llvm::Value *state,
                          unsigned offset, llvm::Value *val) {
  auto *ptr = gepByteOffset(Builder, state, offset);
  Builder.CreateStore(val, ptr);
}

/// Load an i64 from CONTEXT at a given byte offset.
static llvm::Value *loadCtxI64(llvm::IRBuilder<> &Builder, llvm::Value *ctx,
                               unsigned offset) {
  auto *i64_ty = llvm::Type::getInt64Ty(Builder.getContext());
  auto *ptr = gepByteOffset(Builder, ctx, offset);
  return Builder.CreateLoad(i64_ty, ptr);
}

/// Store an i64 to CONTEXT at a given byte offset.
static void storeCtxI64(llvm::IRBuilder<> &Builder, llvm::Value *ctx,
                        unsigned offset, llvm::Value *val) {
  auto *ptr = gepByteOffset(Builder, ctx, offset);
  Builder.CreateStore(val, ptr);
}

/// Load 128 bits from State XMM slot as <2 x i64>.
static llvm::Value *loadStateXMM(llvm::IRBuilder<> &Builder,
                                 llvm::Value *state, unsigned n) {
  auto *i64_ty = llvm::Type::getInt64Ty(Builder.getContext());
  auto *vec_ty = llvm::FixedVectorType::get(i64_ty, 2);
  unsigned off = xmmStateOffset(n);
  auto *ptr = gepByteOffset(Builder, state, off);
  return Builder.CreateLoad(vec_ty, ptr);
}

/// Store 128 bits to State XMM slot from <2 x i64>.
static void storeStateXMM(llvm::IRBuilder<> &Builder, llvm::Value *state,
                           unsigned n, llvm::Value *val) {
  unsigned off = xmmStateOffset(n);
  auto *ptr = gepByteOffset(Builder, state, off);
  Builder.CreateStore(val, ptr);
}

/// Load 128 bits from CONTEXT XMM slot as <2 x i64>.
static llvm::Value *loadCtxXMM(llvm::IRBuilder<> &Builder, llvm::Value *ctx,
                                unsigned n) {
  auto *i64_ty = llvm::Type::getInt64Ty(Builder.getContext());
  auto *vec_ty = llvm::FixedVectorType::get(i64_ty, 2);
  unsigned off = xmmContextOffset(n);
  auto *ptr = gepByteOffset(Builder, ctx, off);
  return Builder.CreateLoad(vec_ty, ptr);
}

/// Store 128 bits to CONTEXT XMM slot from <2 x i64>.
static void storeCtxXMM(llvm::IRBuilder<> &Builder, llvm::Value *ctx,
                         unsigned n, llvm::Value *val) {
  unsigned off = xmmContextOffset(n);
  auto *ptr = gepByteOffset(Builder, ctx, off);
  Builder.CreateStore(val, ptr);
}

}  // namespace

llvm::PreservedAnalyses ResolveForcedExceptionsPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  auto &MAMProxy = AM.getResult<llvm::ModuleAnalysisManagerFunctionProxy>(F);
  auto &M = *F.getParent();

  auto *excinfo =
      MAMProxy.getCachedResult<ExceptionInfoAnalysis>(M);
  if (!excinfo || excinfo->empty())
    return llvm::PreservedAnalyses::all();

  // Look up the RUNTIME_FUNCTION for this function's entry VA.
  // Using the function name (sub_<hex>) is more robust than using the
  // error PC, because remill passes the *next* PC to __remill_error
  // (past the faulting instruction), which can fall outside the
  // RUNTIME_FUNCTION's [begin, end) range for short functions.
  uint64_t func_va = extractEntryVA(F.getName());
  if (func_va == 0)
    return llvm::PreservedAnalyses::all();

  auto *rt_entry = excinfo->lookup(func_va);
  if (!rt_entry || rt_entry->handler_va == 0)
    return llvm::PreservedAnalyses::all();

  auto *lifted =
      MAMProxy.getCachedResult<LiftedFunctionAnalysis>(M);

  // Handler must be a lifted function.
  auto *handler_fn = lifted ? lifted->lookup(rt_entry->handler_va) : nullptr;
  if (!handler_fn)
    return llvm::PreservedAnalyses::all();

  IntrinsicTable table(M);

  // Collect all __remill_error calls in this function.
  struct Candidate {
    llvm::CallInst *CI;
    llvm::Value *error_pc;  // The error PC (SSA value, may not be constant yet)
  };
  llvm::SmallVector<Candidate, 4> candidates;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      if (table.classifyCall(CI) != IntrinsicKind::kError)
        continue;

      candidates.push_back({CI, CI->getArgOperand(1)});
    }
  }

  if (candidates.empty())
    return llvm::PreservedAnalyses::all();

  auto &Ctx = F.getContext();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Get the lifted function type for __omill_dispatch_jump.
  auto *state_ptr_ty = F.getArg(0)->getType();
  auto *mem_ptr_ty = F.getFunctionType()->getReturnType();
  auto *lifted_fn_ty = llvm::FunctionType::get(
      mem_ptr_ty, {state_ptr_ty, i64_ty, mem_ptr_ty}, false);
  auto dispatcher =
      M.getOrInsertFunction("__omill_dispatch_jump", lifted_fn_ty);

  for (auto &[CI, error_pc] : candidates) {
    llvm::IRBuilder<> Builder(CI);
    auto *BB = CI->getParent();

    // Save old successors before we replace the terminator.
    llvm::SmallVector<llvm::BasicBlock *, 4> old_succs(successors(BB));

    llvm::Value *state = CI->getArgOperand(0);
    llvm::Value *mem = CI->getArgOperand(2);

    // (a) Allocate CONTEXT and EXCEPTION_RECORD on the stack.
    auto *ctx_array_ty = llvm::ArrayType::get(i8_ty, kContextSize);
    auto *exrec_array_ty = llvm::ArrayType::get(i8_ty, kExceptionRecordSize);

    // Insert allocas at function entry.
    llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock(),
                                   F.getEntryBlock().getFirstInsertionPt());
    auto *ctx_alloca = EntryBuilder.CreateAlloca(
        ctx_array_ty, nullptr, "exception_ctx");
    ctx_alloca->setAlignment(llvm::Align(kContextAlign));
    auto *exrec_alloca = EntryBuilder.CreateAlloca(
        exrec_array_ty, nullptr, "exception_rec");
    exrec_alloca->setAlignment(llvm::Align(kExceptionRecordAlign));

    // Zero-initialize both.
    Builder.CreateMemSet(ctx_alloca, Builder.getInt8(0), kContextSize,
                         llvm::Align(kContextAlign));
    Builder.CreateMemSet(exrec_alloca, Builder.getInt8(0),
                         kExceptionRecordSize,
                         llvm::Align(kExceptionRecordAlign));

    // (b) Marshal State GPRs -> CONTEXT.
    for (const auto &m : kGPRMappings) {
      auto *val = loadStateI64(Builder, state, m.state_offset);
      storeCtxI64(Builder, ctx_alloca, m.context_offset, val);
    }

    // Marshal XMM0-15: State -> CONTEXT.
    for (unsigned n = 0; n < kXMMCount; ++n) {
      auto *val = loadStateXMM(Builder, state, n);
      storeCtxXMM(Builder, ctx_alloca, n, val);
    }

    // Set CONTEXT.Rip = error PC (the faulting instruction's next-PC).
    // This is an SSA value that becomes constant after FoldProgramCounter.
    storeCtxI64(Builder, ctx_alloca, kContextRipOffset, error_pc);

    // (c) Fill EXCEPTION_RECORD.
    //     ExceptionCode = STATUS_ILLEGAL_INSTRUCTION (0xC000001D)
    auto *exrec_code_ptr = gepByteOffset(Builder, exrec_alloca,
                                          kExRecCodeOffset);
    Builder.CreateStore(Builder.getInt32(kStatusIllegalInstruction),
                        exrec_code_ptr);

    //     ExceptionAddress = error PC
    auto *exrec_addr_ptr = gepByteOffset(Builder, exrec_alloca,
                                          kExRecAddressOffset);
    Builder.CreateStore(error_pc, exrec_addr_ptr);

    // (d) Store handler args into State (Win64 ABI).
    //     RCX = &EXCEPTION_RECORD
    //     RDX = 0 (EstablisherFrame)
    //     R8  = &CONTEXT
    //     R9  = 0 (DispatcherContext)
    auto *exrec_int = Builder.CreatePtrToInt(exrec_alloca, i64_ty);
    storeStateI64(Builder, state, kStateRCX, exrec_int);
    storeStateI64(Builder, state, kStateRDX, Builder.getInt64(0));
    auto *ctx_int = Builder.CreatePtrToInt(ctx_alloca, i64_ty);
    storeStateI64(Builder, state, kStateR8, ctx_int);
    storeStateI64(Builder, state, kStateR9, Builder.getInt64(0));

    // (e) Call the lifted handler.
    auto *handler_result = Builder.CreateCall(
        handler_fn,
        {state, Builder.getInt64(rt_entry->handler_va), mem});

    // (f) Unmarshal CONTEXT -> State (handler may have modified any register).
    for (const auto &m : kGPRMappings) {
      auto *val = loadCtxI64(Builder, ctx_alloca, m.context_offset);
      storeStateI64(Builder, state, m.state_offset, val);
    }

    // Unmarshal XMM0-15: CONTEXT -> State.
    for (unsigned n = 0; n < kXMMCount; ++n) {
      auto *val = loadCtxXMM(Builder, ctx_alloca, n);
      storeStateXMM(Builder, state, n, val);
    }

    // (g) Load new RIP from CONTEXT.
    auto *new_rip = loadCtxI64(Builder, ctx_alloca, kContextRipOffset);

    // (h) Tail-dispatch to new RIP.
    auto *dispatch_result =
        Builder.CreateCall(dispatcher, {state, new_rip, handler_result});
    auto *new_term = Builder.CreateRet(dispatch_result);

    // Replace uses of the original __remill_error call and erase it.
    CI->replaceAllUsesWith(llvm::PoisonValue::get(CI->getType()));
    CI->eraseFromParent();

    // Erase all dead instructions after the new terminator.
    while (&BB->back() != new_term) {
      auto &dead = BB->back();
      if (!dead.use_empty())
        dead.replaceAllUsesWith(llvm::PoisonValue::get(dead.getType()));
      dead.eraseFromParent();
    }

    // Update PHI nodes: dispatch_jump + ret has no BB successors,
    // so all old successors lost this block as a predecessor.
    for (auto *succ : old_succs)
      succ->removePredecessor(BB);
  }

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
