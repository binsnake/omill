#if OMILL_ENABLE_Z3

#include "RandomIRVerifier.h"

#include "omill/Passes/OptimizeState.h"
#include "omill/Passes/OutlineConstantStackData.h"
#include "omill/Passes/SimplifyVectorReassembly.h"
#include "omill/Utils/TranslationValidator.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

namespace omill {
namespace test {

static const char *kDataLayout =
    "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
    "n8:16:32:64-S128";

RandomIRVerifier::RandomIRVerifier(z3::context &ctx, uint64_t seed)
    : rng_(seed), ctx_(ctx) {}

std::unique_ptr<llvm::LLVMContext> RandomIRVerifier::makeLLVMContext() {
  return std::make_unique<llvm::LLVMContext>();
}

std::unique_ptr<llvm::Module> RandomIRVerifier::makeModule(
    llvm::LLVMContext &Ctx) {
  auto M = std::make_unique<llvm::Module>("fuzz", Ctx);
  M->setDataLayout(kDataLayout);
  return M;
}

static void setupAnalyses(llvm::PassBuilder &PB,
                           llvm::LoopAnalysisManager &LAM,
                           llvm::FunctionAnalysisManager &FAM,
                           llvm::CGSCCAnalysisManager &CGAM,
                           llvm::ModuleAnalysisManager &MAM) {
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
}

void RandomIRVerifier::runPassOnFunction(PassKind kind, llvm::Function &F) {
  llvm::FunctionPassManager FPM;

  switch (kind) {
    case PassKind::CoalesceByteReassembly:
    case PassKind::CollapsePartialXMMWrites:
    case PassKind::SimplifyVectorFlagComputation:
    case PassKind::FoldConstantVectorChains:
      FPM.addPass(SimplifyVectorReassemblyPass());
      break;
    case PassKind::DeadStateRoundtripElimination:
      FPM.addPass(OptimizeStatePass(OptimizePhases::Roundtrip));
      break;
    case PassKind::EliminateRedundantByteStores:
      FPM.addPass(OptimizeStatePass(OptimizePhases::RedundantBytes));
      break;
    case PassKind::OutlineConstantStackData:
      FPM.addPass(OutlineConstantStackDataPass());
      break;
  }

  llvm::PassBuilder PB;
  llvm::LoopAnalysisManager LAM;
  llvm::FunctionAnalysisManager FAM;
  llvm::CGSCCAnalysisManager CGAM;
  llvm::ModuleAnalysisManager MAM;
  setupAnalyses(PB, LAM, FAM, CGAM, MAM);
  FPM.run(F, FAM);
}

// ============================================================================
// Pattern generators
// ============================================================================

llvm::Function *RandomIRVerifier::genByteReassembly(llvm::Module &M,
                                                     llvm::LLVMContext &Ctx) {
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  // Randomly choose reassembly width: 2, 4, or 8 bytes.
  unsigned widths[] = {2, 4, 8};
  unsigned num_bytes = widths[rng_() % 3];

  auto *result_ty = llvm::Type::getIntNTy(Ctx, num_bytes * 8);
  auto *fn_ty = llvm::FunctionType::get(result_ty, {v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *src = F->getArg(0);

  // Choose piece width: i8, i16, or i32 (must divide num_bytes).
  unsigned piece_bits = 8;
  if (num_bytes >= 4 && (rng_() % 2))
    piece_bits = (num_bytes >= 4 && (rng_() % 2)) ? 32 : 16;
  else if (num_bytes >= 2 && (rng_() % 2))
    piece_bits = 16;

  unsigned piece_bytes = piece_bits / 8;
  // Ensure num_bytes is divisible by piece_bytes.
  if (num_bytes % piece_bytes != 0)
    piece_bits = 8, piece_bytes = 1;

  // Random starting byte offset, aligned to piece_bytes.
  unsigned max_start = (16 - num_bytes) / piece_bytes;
  unsigned start_byte = (rng_() % (max_start + 1)) * piece_bytes;

  unsigned num_pieces = num_bytes / piece_bytes;
  unsigned num_elements = 16 / piece_bytes;

  auto *piece_ty = llvm::Type::getIntNTy(Ctx, piece_bits);
  auto *vec_ty = llvm::FixedVectorType::get(piece_ty, num_elements);
  auto *bc = B.CreateBitCast(src, vec_ty, "bc");

  // Build OR tree.
  llvm::Value *acc = nullptr;
  for (unsigned i = 0; i < num_pieces; ++i) {
    unsigned elem_idx = start_byte / piece_bytes + i;
    auto *elem = B.CreateExtractElement(bc, B.getInt64(elem_idx),
                                         "e" + std::to_string(i));
    auto *ext = B.CreateZExt(elem, result_ty, "z" + std::to_string(i));
    if (i > 0) {
      auto *shifted = B.CreateShl(
          ext, llvm::ConstantInt::get(result_ty, i * piece_bits),
          "s" + std::to_string(i));
      acc = B.CreateOr(acc, shifted, "or" + std::to_string(i));
      if (auto *BO = llvm::dyn_cast<llvm::PossiblyDisjointInst>(acc))
        BO->setIsDisjoint(true);
    } else {
      acc = ext;
    }
  }

  B.CreateRet(acc);
  return F;
}

llvm::Function *RandomIRVerifier::genPartialXMMWrite(llvm::Module &M,
                                                      llvm::LLVMContext &Ctx) {
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *v16i8_ty = llvm::FixedVectorType::get(i8_ty, 16);

  auto *fn_ty = llvm::FunctionType::get(i8_ty, {v16i8_ty, v16i8_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *new_val = F->getArg(0);
  auto *old_val = F->getArg(1);

  // Random split point (1-15): first N from new_val, rest from old_val.
  unsigned split = 1 + (rng_() % 15);
  llvm::SmallVector<int, 16> mask;
  for (unsigned i = 0; i < 16; ++i) {
    if (i < split)
      mask.push_back(i);           // from new_val
    else
      mask.push_back(16 + i);      // from old_val
  }

  auto *blended = B.CreateShuffleVector(new_val, old_val, mask, "blended");

  // Random extract index.
  unsigned extract_idx = rng_() % 16;
  auto *extracted = B.CreateExtractElement(blended, B.getInt64(extract_idx),
                                            "byte");
  B.CreateRet(extracted);
  return F;
}

llvm::Function *RandomIRVerifier::genVectorFlagComputation(
    llvm::Module &M, llvm::LLVMContext &Ctx) {
  // Choose random vector width: 4, 8, or 16.
  unsigned widths[] = {4, 8, 16};
  unsigned N = widths[rng_() % 3];

  auto *i1_ty = llvm::Type::getInt1Ty(Ctx);
  auto *i1_vN_ty = llvm::FixedVectorType::get(i1_ty, N);

  // Choose sext element width: 8, 16, or 32.
  unsigned elem_widths[] = {8, 16, 32};
  unsigned elem_w = elem_widths[rng_() % 3];

  auto *elem_ty = llvm::Type::getIntNTy(Ctx, elem_w);
  auto *sext_vN_ty = llvm::FixedVectorType::get(elem_ty, N);

  // Choose one of: direct extract, and-mask, or lshr patterns.
  unsigned pattern = rng_() % 3;

  llvm::Type *ret_ty = nullptr;
  if (pattern == 0) {
    // Direct extract from sext result.
    ret_ty = elem_ty;
  } else {
    // And-mask or lshr: may bitcast to wider type.
    ret_ty = elem_ty;  // simplified
  }

  auto *fn_ty = llvm::FunctionType::get(ret_ty, {i1_vN_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *cmp = F->getArg(0);
  auto *sext = B.CreateSExt(cmp, sext_vN_ty, "sext");

  unsigned lane = rng_() % N;

  if (pattern == 0) {
    // Direct extractelement from sext.
    auto *extract = B.CreateExtractElement(sext, B.getInt64(lane), "byte");
    B.CreateRet(extract);
  } else if (pattern == 1) {
    // Extract + AND with 1.
    auto *extract = B.CreateExtractElement(sext, B.getInt64(lane), "byte");
    auto *masked = B.CreateAnd(extract, llvm::ConstantInt::get(elem_ty, 1),
                                "bit");
    B.CreateRet(masked);
  } else {
    // Extract + AND with power-of-2.
    auto *extract = B.CreateExtractElement(sext, B.getInt64(lane), "byte");
    unsigned bit = rng_() % elem_w;
    uint64_t mask_val = 1ULL << bit;
    auto *masked = B.CreateAnd(extract,
                                llvm::ConstantInt::get(elem_ty, mask_val),
                                "bit");
    B.CreateRet(masked);
  }

  return F;
}

llvm::Function *RandomIRVerifier::genStateRoundtrip(llvm::Module &M,
                                                     llvm::LLVMContext &Ctx) {
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *callee = llvm::Function::Create(
      fn_ty, llvm::Function::ExternalLinkage, "sub_402000", M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Random State offset (aligned to 8).
  unsigned offset = (rng_() % 400) * 8;

  // Random value to store.
  uint64_t val = rng_();

  auto *gep1 = B.CreateConstGEP1_64(B.getInt8Ty(), state, offset, "ptr1");
  B.CreateStore(B.getInt64(val), gep1);
  auto *call = B.CreateCall(callee, {state, B.getInt64(0), mem});

  // 50% chance: pure roundtrip vs modified value.
  bool is_roundtrip = (rng_() % 2) == 0;

  auto *gep2 = B.CreateConstGEP1_64(B.getInt8Ty(), state, offset, "ptr2");
  auto *loaded = B.CreateLoad(i64_ty, gep2, "loaded");

  llvm::Value *store_val = loaded;
  if (!is_roundtrip) {
    store_val = B.CreateAdd(loaded, B.getInt64(rng_() % 100 + 1), "modified");
  }

  auto *gep3 = B.CreateConstGEP1_64(B.getInt8Ty(), state, offset, "ptr3");
  B.CreateStore(store_val, gep3);
  B.CreateRet(call);

  return F;
}

llvm::Function *RandomIRVerifier::genRedundantByteStore(
    llvm::Module &M, llvm::LLVMContext &Ctx) {
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  auto *fn_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Random wide store offset.
  unsigned wide_offset = (rng_() % 400) * 8;
  uint64_t wide_val = rng_();

  auto *gep_wide =
      B.CreateConstGEP1_64(B.getInt8Ty(), state, wide_offset, "wide");
  B.CreateStore(B.getInt64(wide_val), gep_wide);

  // Narrow store within the wide range.
  unsigned byte_offset_in_wide = rng_() % 8;
  unsigned narrow_offset = wide_offset + byte_offset_in_wide;

  // 50% chance: matching byte (redundant) or different byte.
  uint8_t matching_byte =
      (uint8_t)((wide_val >> (byte_offset_in_wide * 8)) & 0xFF);
  bool is_redundant = (rng_() % 2) == 0;
  uint8_t narrow_val = is_redundant ? matching_byte : (uint8_t)(rng_() & 0xFF);

  auto *gep_narrow =
      B.CreateConstGEP1_64(B.getInt8Ty(), state, narrow_offset, "narrow");
  B.CreateStore(llvm::ConstantInt::get(i8_ty, narrow_val), gep_narrow);

  B.CreateRet(mem);
  return F;
}

llvm::Function *RandomIRVerifier::genConstantVectorChain(
    llvm::Module &M, llvm::LLVMContext &Ctx) {
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *v4i32_ty = llvm::FixedVectorType::get(i32_ty, 4);

  auto *fn_ty = llvm::FunctionType::get(v4i32_ty, {}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  // 50% chance: shuffle of constants or insert chain.
  if (rng_() % 2) {
    // Shuffle of two constant vectors.
    llvm::SmallVector<llvm::Constant *, 4> elems1, elems2;
    for (unsigned i = 0; i < 4; ++i) {
      elems1.push_back(
          llvm::ConstantInt::get(i32_ty, (uint32_t)rng_()));
      elems2.push_back(
          llvm::ConstantInt::get(i32_ty, (uint32_t)rng_()));
    }
    auto *c1 = llvm::ConstantVector::get(elems1);
    auto *c2 = llvm::ConstantVector::get(elems2);

    // Random shuffle mask (values 0-7).
    llvm::SmallVector<int, 4> mask;
    for (unsigned i = 0; i < 4; ++i)
      mask.push_back(rng_() % 8);

    auto *shuffled = B.CreateShuffleVector(c1, c2, mask, "shuffled");
    B.CreateRet(shuffled);
  } else {
    // Insert chain from zeroinitializer.
    llvm::Value *vec = llvm::ConstantAggregateZero::get(v4i32_ty);
    unsigned num_inserts = 1 + (rng_() % 4);
    for (unsigned i = 0; i < num_inserts; ++i) {
      unsigned idx = rng_() % 4;
      auto *val = llvm::ConstantInt::get(i32_ty, (uint32_t)rng_());
      vec = B.CreateInsertElement(vec, val, B.getInt64(idx),
                                   "ins" + std::to_string(i));
    }
    B.CreateRet(vec);
  }

  return F;
}

llvm::Function *RandomIRVerifier::genConstantStackData(llvm::Module &M,
                                                        llvm::LLVMContext &Ctx) {
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);

  // Random alloca size: 8 to 64 bytes (aligned to 4).
  unsigned size = ((rng_() % 15) + 2) * 4;

  auto *fn_ty = llvm::FunctionType::get(i64_ty, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  llvm::IRBuilder<> B(entry);

  auto *alloca = B.CreateAlloca(llvm::ArrayType::get(B.getInt8Ty(), size));

  // Store random constants at i32-aligned offsets.
  unsigned num_stores = size / 4;
  for (unsigned i = 0; i < num_stores; ++i) {
    auto *gep = B.CreateConstGEP1_64(B.getInt8Ty(), alloca, i * 4);
    B.CreateStore(B.getInt32((uint32_t)rng_()), gep);
  }

  // Load first 8 bytes.
  auto *val = B.CreateLoad(i64_ty, alloca);
  B.CreateRet(val);

  return F;
}

// ============================================================================
// Main fuzz loop
// ============================================================================

RandomIRVerifier::Result RandomIRVerifier::fuzzPass(PassKind kind,
                                                     unsigned iterations) {
  Result result;
  result.all_passed = true;
  result.num_tested = 0;

  for (unsigned i = 0; i < iterations; ++i) {
    auto LLVMCtx = makeLLVMContext();
    auto M = makeModule(*LLVMCtx);

    llvm::Function *F = nullptr;
    std::vector<unsigned> compare_offsets;

    switch (kind) {
      case PassKind::CoalesceByteReassembly:
        F = genByteReassembly(*M, *LLVMCtx);
        break;
      case PassKind::CollapsePartialXMMWrites:
        F = genPartialXMMWrite(*M, *LLVMCtx);
        break;
      case PassKind::SimplifyVectorFlagComputation:
        F = genVectorFlagComputation(*M, *LLVMCtx);
        break;
      case PassKind::DeadStateRoundtripElimination:
        F = genStateRoundtrip(*M, *LLVMCtx);
        break;
      case PassKind::EliminateRedundantByteStores:
        F = genRedundantByteStore(*M, *LLVMCtx);
        break;
      case PassKind::FoldConstantVectorChains:
        F = genConstantVectorChain(*M, *LLVMCtx);
        break;
      case PassKind::OutlineConstantStackData:
        F = genConstantStackData(*M, *LLVMCtx);
        break;
    }

    if (!F) continue;

    // Verify the generated IR is valid before running.
    if (llvm::verifyFunction(*F, nullptr)) continue;

    TranslationValidator validator(ctx_);
    if (!compare_offsets.empty())
      validator.setCompareOffsets(compare_offsets);
    validator.snapshotBefore(*F);

    runPassOnFunction(kind, *F);

    if (llvm::verifyFunction(*F, nullptr)) {
      result.all_passed = false;
      result.first_failure =
          "Iteration " + std::to_string(i) +
          ": pass produced invalid IR";
      return result;
    }

    auto vr = validator.verify(*F);
    result.num_tested++;

    if (!vr.equivalent) {
      result.all_passed = false;
      result.first_failure =
          "Iteration " + std::to_string(i) +
          ": semantic equivalence failed: " + vr.counterexample;
      return result;
    }
  }

  return result;
}

}  // namespace test
}  // namespace omill

#endif  // OMILL_ENABLE_Z3
