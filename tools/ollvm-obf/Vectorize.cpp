#include "Vectorize.h"
#include "PassFilter.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/ValueHandle.h>

#include <algorithm>
#include <random>

namespace ollvm {

namespace {

bool isSupportedOpcode(unsigned op) {
  switch (op) {
  case llvm::Instruction::Add:
  case llvm::Instruction::Sub:
  case llvm::Instruction::Xor:
  case llvm::Instruction::And:
  case llvm::Instruction::Or:
  case llvm::Instruction::Mul:
    return true;
  default:
    return false;
  }
}

bool isZeroLane(llvm::Value *idx) {
  auto *ci = llvm::dyn_cast<llvm::ConstantInt>(idx);
  return ci && ci->isZero();
}

// ---------------------------------------------------------------------------
// LaneContext — per-width vector state (<4 x i32> or <2 x i64>).
// ---------------------------------------------------------------------------

struct LaneContext {
  llvm::FixedVectorType *vec_ty = nullptr;
  llvm::Constant *zero_vec = nullptr;
  llvm::ConstantInt *idx_zero = nullptr;
  llvm::IntegerType *scalar_ty = nullptr;
  unsigned num_lanes = 0;
  std::mt19937 *rng = nullptr;

  // Lazy bitwise-mode helper splats (materialised on first Add/Sub).
  llvm::Value *one_vec = nullptr;
  llvm::Value *all_ones_vec = nullptr;

  // Constant splat cache — keyed on ConstantInt* (unique per type+value pair
  // in the LLVMContext). Cannot use uint64_t key because DenseMap<uint64_t,...>
  // reserves ~0ULL as empty sentinel, colliding with the constant -1.
  llvm::DenseMap<llvm::ConstantInt *, llvm::Value *> const_splats;

  // Scalar→vector reuse map (chain optimisation + repeated-operand dedup).
  llvm::DenseMap<llvm::Value *, llvm::WeakTrackingVH> scalar_to_vector;

  // Tracked ExtractElementInsts for targeted dead-code cleanup.
  llvm::SmallVector<llvm::ExtractElementInst *, 32> created_extracts;

  void init(llvm::LLVMContext &ctx, unsigned bits) {
    scalar_ty = llvm::IntegerType::get(ctx, bits);
    num_lanes = (bits == 64) ? 2 : 4;
    vec_ty = llvm::FixedVectorType::get(scalar_ty, num_lanes);
    zero_vec = llvm::ConstantAggregateZero::get(vec_ty);
    // ExtractElement / InsertElement indices are always i32.
    idx_zero = llvm::ConstantInt::get(llvm::Type::getInt32Ty(ctx), 0);
  }

  void ensureBitwiseSplats(llvm::IRBuilder<> &entry_builder) {
    if (!one_vec) {
      one_vec = entry_builder.CreateVectorSplat(
          num_lanes, llvm::ConstantInt::get(scalar_ty, 1));
      all_ones_vec = entry_builder.CreateVectorSplat(
          num_lanes, llvm::ConstantInt::getSigned(scalar_ty, -1));
    }
  }

  llvm::Value *getConstSplat(llvm::IRBuilder<> &/*entry_builder*/,
                             llvm::ConstantInt *ci) {
    // Ensure the constant matches the lane scalar width.
    if (ci->getType() != scalar_ty) {
      ci = llvm::cast<llvm::ConstantInt>(llvm::ConstantInt::get(
               scalar_ty, ci->getValue().zextOrTrunc(
                   scalar_ty->getBitWidth())));
    }
    auto [it, inserted] = const_splats.try_emplace(ci, nullptr);
    if (!inserted)
      return it->second;
    // Build a ConstantVector directly — immune to instruction erasure.
    llvm::SmallVector<llvm::Constant *, 4> elts(num_lanes, ci);
    auto *v = llvm::ConstantVector::get(elts);
    it->second = v;
    return v;
  }

  void cleanupDeadExtracts() {
    for (auto *EE : created_extracts) {
      if (!EE->use_empty())
        continue;
      // If erasing this EE makes its vector producer dead, clean that up too.
      // This prevents orphaned vector binops from bloating the IR.
      auto *producer = llvm::dyn_cast<llvm::Instruction>(EE->getVectorOperand());
      EE->eraseFromParent();
      if (producer && producer->use_empty())
        producer->eraseFromParent();
    }
  }
};

/// Fill lanes 1+ with splitmix-style noise derived from the stored value.
/// Each lane applies a 2-step hash with unique random constants, making the
/// relationship non-trivially invertible.  A symbolic engine cannot identify
/// lane 0 as the "real" value by checking for simple algebraic relationships.
llvm::Value *fillNoiseLanes(llvm::IRBuilder<> &builder, llvm::Value *packed,
                            llvm::Value *value, LaneContext &lc) {
  if (!lc.rng)
    return packed;
  auto &rng = *lc.rng;
  auto *i32Ty = llvm::Type::getInt32Ty(builder.getContext());
  unsigned bits = lc.scalar_ty->getIntegerBitWidth();

  for (unsigned lane = 1; lane < lc.num_lanes; ++lane) {
    // Per-lane unique constants.  Multipliers forced odd for invertibility
    // irrelevance (full-period in modular arithmetic).
    uint64_t m1 = std::uniform_int_distribution<uint64_t>(1, UINT64_MAX)(rng) | 1ULL;
    uint64_t m2 = std::uniform_int_distribution<uint64_t>(1, UINT64_MAX)(rng) | 1ULL;
    uint64_t k  = std::uniform_int_distribution<uint64_t>(0, UINT64_MAX)(rng);
    unsigned s1 = std::uniform_int_distribution<unsigned>(1, bits / 2)(rng);
    unsigned s2 = std::uniform_int_distribution<unsigned>(1, bits / 2)(rng);

    auto *cm1 = llvm::ConstantInt::get(lc.scalar_ty, m1);
    auto *cm2 = llvm::ConstantInt::get(lc.scalar_ty, m2);
    auto *ck  = llvm::ConstantInt::get(lc.scalar_ty, k);

    // Step 1: h = (value ^ (value >> s1)) * m1
    auto *shr1 = builder.CreateLShr(value, s1);
    auto *xor1 = builder.CreateXor(value, shr1);
    auto *h    = builder.CreateMul(xor1, cm1);

    // Step 2: noise = ((h ^ (h >> s2)) * m2) ^ k
    auto *shr2  = builder.CreateLShr(h, s2);
    auto *xor2  = builder.CreateXor(h, shr2);
    auto *mul2  = builder.CreateMul(xor2, cm2);
    auto *noise = builder.CreateXor(mul2, ck);

    auto *idx = llvm::ConstantInt::get(i32Ty, lane);
    packed = builder.CreateInsertElement(packed, noise, idx);
  }
  return packed;
}

// ---------------------------------------------------------------------------
// Scalar → vector lifting
// ---------------------------------------------------------------------------

/// Lift a scalar value into lane 0 of the matching vector type.
///
/// Caches results per basic block so repeated uses of the same scalar share
/// one InsertElement without risking cross-BB dominance violations.
/// When \p reuse_vector_data is set, additionally reuses the source vector of
/// extractelement instructions originating from vectorized stack data.
llvm::Value *liftLane0ToVector(llvm::IRBuilder<> &builder, llvm::Value *v,
                               LaneContext &lc, bool reuse_vector_data,
                               const llvm::DominatorTree &DT,
                               llvm::Instruction *insertPt) {
  // Check cache — reuse values that dominate the insertion point.
  if (auto it = lc.scalar_to_vector.find(v); it != lc.scalar_to_vector.end()) {
    llvm::Value *cached = it->second;
    if (!cached) {
      // WeakTrackingVH nulled out — entry is stale, remove and re-create.
      lc.scalar_to_vector.erase(it);
    } else if (cached->getType() == lc.vec_ty) {
      if (auto *ci = llvm::dyn_cast<llvm::Instruction>(cached)) {
        if (DT.dominates(ci, insertPt))
          return cached;
      } else {
        return cached;
      }
    }
  }

  // Data-aware mode: if this scalar came from extractelement %vec, 0,
  // reuse the vector payload directly to keep data in vector space.
  // Only safe if the vector dominates the insertion point.
  if (reuse_vector_data) {
    if (auto *ee = llvm::dyn_cast<llvm::ExtractElementInst>(v)) {
      if (ee->getVectorOperand()->getType() == lc.vec_ty &&
          isZeroLane(ee->getIndexOperand())) {
        auto *vec = ee->getVectorOperand();
        bool safe = !llvm::isa<llvm::Instruction>(vec) ||
                    DT.dominates(llvm::cast<llvm::Instruction>(vec), insertPt);
        if (safe) {
          lc.scalar_to_vector[v] = vec;
          return vec;
        }
      }
    }
  }

  // Coerce scalar width to match the lane type if needed.
  // Cache the result under the ORIGINAL value (before coercion) so that
  // repeated lookups with the same original key hit the cache.
  auto *original = v;
  if (v->getType() != lc.scalar_ty) {
    unsigned srcBits = v->getType()->getIntegerBitWidth();
    unsigned dstBits = lc.scalar_ty->getBitWidth();
    if (srcBits < dstBits)
      v = builder.CreateZExt(v, lc.scalar_ty);
    else
      v = builder.CreateTrunc(v, lc.scalar_ty);
  }
  auto *lifted = builder.CreateInsertElement(lc.zero_vec, v, lc.idx_zero);
  lifted = fillNoiseLanes(builder, lifted, v, lc);
  lc.scalar_to_vector[original] = lifted;
  return lifted;
}

// ---------------------------------------------------------------------------
// Vector binary-op construction (with optional bitwise lowering)
// ---------------------------------------------------------------------------

llvm::Value *buildVectorBitwiseAdd(llvm::IRBuilder<> &builder,
                                   llvm::Value *lhs, llvm::Value *rhs,
                                   llvm::Value *one_vec) {
  // a + b == (a ^ b) + ((a & b) << 1)
  auto *sum = builder.CreateXor(lhs, rhs);
  auto *carry = builder.CreateAnd(lhs, rhs);
  auto *carry2 = builder.CreateShl(carry, one_vec);
  return builder.CreateAdd(sum, carry2);
}

llvm::Value *buildVectorBitwiseSub(llvm::IRBuilder<> &builder,
                                   llvm::Value *lhs, llvm::Value *rhs,
                                   llvm::Value *one_vec,
                                   llvm::Value *all_ones_vec) {
  // a - b == (a ^ b) - (((~a) & b) << 1)
  auto *diff = builder.CreateXor(lhs, rhs);
  auto *not_lhs = builder.CreateXor(lhs, all_ones_vec);
  auto *borrow = builder.CreateAnd(not_lhs, rhs);
  auto *borrow2 = builder.CreateShl(borrow, one_vec);
  return builder.CreateSub(diff, borrow2);
}

llvm::Value *buildVectorBitwiseMul(llvm::IRBuilder<> &builder,
                                   llvm::Value *lhs, llvm::Value *rhs,
                                   LaneContext &lc) {
  // Schoolbook half-width decomposition:
  //   a * b = (a_lo * b_lo) + ((a_lo * b_hi) << half) + ((a_hi * b_lo) << half)
  // All arithmetic mod 2^N, so the a_hi*b_hi term is discarded.
  unsigned bits = lc.scalar_ty->getBitWidth();
  unsigned half = bits / 2;
  auto *halfShift = llvm::ConstantInt::get(lc.scalar_ty, half);
  llvm::SmallVector<llvm::Constant *, 4> shiftElts(lc.num_lanes, halfShift);
  auto *halfVec = llvm::ConstantVector::get(shiftElts);

  auto *maskVal = llvm::ConstantInt::get(lc.scalar_ty,
      (uint64_t(1) << half) - 1);
  llvm::SmallVector<llvm::Constant *, 4> maskElts(lc.num_lanes, maskVal);
  auto *maskVec = llvm::ConstantVector::get(maskElts);

  auto *a_lo = builder.CreateAnd(lhs, maskVec);
  auto *a_hi = builder.CreateLShr(lhs, halfVec);
  auto *b_lo = builder.CreateAnd(rhs, maskVec);
  auto *b_hi = builder.CreateLShr(rhs, halfVec);

  auto *lo_lo = builder.CreateMul(a_lo, b_lo);
  auto *lo_hi = builder.CreateShl(builder.CreateMul(a_lo, b_hi), halfVec);
  auto *hi_lo = builder.CreateShl(builder.CreateMul(a_hi, b_lo), halfVec);

  return builder.CreateAdd(lo_lo, builder.CreateAdd(lo_hi, hi_lo));
}

llvm::Value *buildVectorBinOp(llvm::IRBuilder<> &builder, unsigned opcode,
                              llvm::Value *va, llvm::Value *vb,
                              const VectorizeOptions &opts, LaneContext &lc) {
  if (!opts.vectorize_bitwise) {
    return builder.CreateBinOp(
        static_cast<llvm::Instruction::BinaryOps>(opcode), va, vb);
  }

  if (opcode == llvm::Instruction::Add) {
    return buildVectorBitwiseAdd(builder, va, vb, lc.one_vec);
  }

  if (opcode == llvm::Instruction::Sub) {
    return buildVectorBitwiseSub(builder, va, vb, lc.one_vec,
                                 lc.all_ones_vec);
  }

  if (opcode == llvm::Instruction::Mul) {
    return buildVectorBitwiseMul(builder, va, vb, lc);
  }

  return builder.CreateBinOp(
      static_cast<llvm::Instruction::BinaryOps>(opcode), va, vb);
}

// ---------------------------------------------------------------------------
// Stack-data vectorization (alloca → vector alloca with lane-0 access)
// ---------------------------------------------------------------------------

/// Convert scalar integer allocas of the given width into vector allocas.
/// Loads become vector-load + extractelement; stores become insertelement +
/// vector-store.  Works for both i32 → <4 x i32> and i64 → <2 x i64>.
void vectorizeStackData(llvm::Function &F, LaneContext &lc) {
  if (F.isDeclaration())
    return;

  llvm::SmallVector<llvm::AllocaInst *, 16> candidates;
  llvm::BasicBlock &entry = F.getEntryBlock();

  for (auto &I : entry) {
    auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I);
    if (!alloca)
      continue;
    if (alloca->isArrayAllocation())
      continue;
    if (alloca->getAllocatedType() != lc.scalar_ty)
      continue;
    // Skip allocas with uses in multiple basic blocks — these are cross-block
    // communication variables (e.g. CFF switch_var, PHI-demote allocas from
    // flattening). Vectorizing them creates cross-block vector loads that
    // violate domination when the data-aware path reuses them.
    {
      llvm::BasicBlock *singleBB = nullptr;
      bool multiBlock = false;
      for (llvm::User *U : alloca->users()) {
        auto *UI = llvm::dyn_cast<llvm::Instruction>(U);
        if (!UI) { multiBlock = true; break; }
        if (!singleBB) singleBB = UI->getParent();
        else if (UI->getParent() != singleBB) { multiBlock = true; break; }
      }
      if (multiBlock)
        continue;
    }

    bool supported = true;
    for (llvm::User *U : alloca->users()) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(U)) {
        if (LI->isVolatile() || LI->isAtomic() ||
            LI->getPointerOperand() != alloca) {
          supported = false;
          break;
        }
        continue;
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
        if (SI->isVolatile() || SI->isAtomic() ||
            SI->getPointerOperand() != alloca ||
            SI->getValueOperand()->getType() != lc.scalar_ty) {
          supported = false;
          break;
        }
        continue;
      }
      if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(U)) {
        switch (II->getIntrinsicID()) {
        case llvm::Intrinsic::lifetime_start:
        case llvm::Intrinsic::lifetime_end:
        case llvm::Intrinsic::dbg_declare:
        case llvm::Intrinsic::dbg_value:
          continue;
        default:
          break;
        }
      }

      supported = false;
      break;
    }

    if (supported)
      candidates.push_back(alloca);
  }

  // Both <4 x i32> and <2 x i64> are 128-bit — 16-byte alignment for SSE.
  const llvm::Align vec_align(16);

  for (auto *alloca : candidates) {
    llvm::Instruction *insert_pt = alloca->getNextNode();
    if (!insert_pt)
      insert_pt = entry.getTerminator();

    llvm::IRBuilder<> alloca_builder(insert_pt);
    auto *vec_alloca = alloca_builder.CreateAlloca(lc.vec_ty, nullptr);
    vec_alloca->setAlignment(vec_align);

    // Collect users before mutation (iterator invalidation).
    llvm::SmallVector<llvm::Instruction *, 16> users;
    for (llvm::User *U : alloca->users()) {
      if (auto *I = llvm::dyn_cast<llvm::Instruction>(U))
        users.push_back(I);
    }

    bool has_real_users = false;
    for (auto *U : users) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(U)) {
        has_real_users = true;
        llvm::IRBuilder<> b(LI);
        auto *vload = b.CreateAlignedLoad(lc.vec_ty, vec_alloca, vec_align);
        auto *lane0 = b.CreateExtractElement(vload, lc.idx_zero);
        LI->replaceAllUsesWith(lane0);
        LI->eraseFromParent();
        continue;
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
        has_real_users = true;
        llvm::IRBuilder<> b(SI);
        auto *packed = b.CreateInsertElement(lc.zero_vec,
                                              SI->getValueOperand(), lc.idx_zero);
        packed = fillNoiseLanes(b, packed, SI->getValueOperand(), lc);
        b.CreateAlignedStore(packed, vec_alloca, vec_align);
        SI->eraseFromParent();
        continue;
      }

      // Erase lifetime/dbg intrinsics — they reference the old scalar alloca
      // and would prevent its cleanup.
      if (auto *II = llvm::dyn_cast<llvm::IntrinsicInst>(U)) {
        II->eraseFromParent();
        continue;
      }
    }

    // Erase the old scalar alloca (all users removed above).
    // If the alloca had no real loads/stores, also remove the dead vec_alloca.
    if (alloca->use_empty())
      alloca->eraseFromParent();
    if (!has_real_users && vec_alloca->use_empty())
      vec_alloca->eraseFromParent();
  }
}

// ---------------------------------------------------------------------------
// Per-function transform driver
// ---------------------------------------------------------------------------

void vectorizeFunction(llvm::Function &F, std::mt19937 &rng,
                       const VectorizeOptions &opts,
                       const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg))
    return;

  std::uniform_int_distribution<int> percent(0, 99);

  // Collect eligible instructions (i32 always; i64 when enabled).
  // Use WeakTrackingVH so we can detect if instructions are deleted by
  // vectorizeStackData or by earlier iterations of the loop below.
  llvm::SmallVector<llvm::WeakTrackingVH, 32> work;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!bin)
        continue;
      auto *ty = bin->getType();
      if (!ty->isIntegerTy(32) &&
          !(opts.vectorize_i64 && ty->isIntegerTy(64)))
        continue;
      if (!isSupportedOpcode(bin->getOpcode()))
        continue;
      // Skip constant-only expressions.
      if (llvm::isa<llvm::Constant>(bin->getOperand(0)) &&
          llvm::isa<llvm::Constant>(bin->getOperand(1)))
        continue;
      work.push_back(bin);
    }
  }

  // Early exit — skip all setup when there's nothing to do.
  if (work.empty())
    return;

  // NOTE: DomTree must be built AFTER vectorizeStackData because that pass
  // erases/inserts instructions, invalidating the instruction-level ordering
  // cache that DominatorTree::dominates(Inst*, Inst*) uses for same-block queries.

  auto &ctx = F.getContext();

  LaneContext lc32;
  lc32.init(ctx, 32);
  lc32.rng = &rng;

  LaneContext lc64;
  if (opts.vectorize_i64) {
    lc64.init(ctx, 64);
    lc64.rng = &rng;
  }

  llvm::IRBuilder<> entry_builder(&*F.getEntryBlock().getFirstInsertionPt());

  if (opts.vectorize_data) {
    vectorizeStackData(F, lc32);
    if (opts.vectorize_i64)
      vectorizeStackData(F, lc64);
  }

  // Compute DomTree AFTER vectorizeStackData — that pass erases/inserts
  // instructions, invalidating DomTree's instruction-ordering cache.
  llvm::DominatorTree DT(F);

  const unsigned threshold = std::min(opts.transform_percent, 100u);

  for (auto &wvh : work) {
    // Skip deleted instructions (erased by vectorizeStackData or earlier iter).
    if (!wvh)
      continue;
    auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(static_cast<llvm::Value *>(wvh));
    if (!bin)
      continue;

    // Apply to configured percent of eligible ops.
    if (threshold == 0 || percent(rng) >= static_cast<int>(threshold))
      continue;

    // Guard: skip if operand types changed since worklist collection,
    // or if the instruction's width isn't enabled (e.g. i64 with !vectorize_i64).
    bool is_i32 = bin->getType()->isIntegerTy(32);
    bool is_i64 = bin->getType()->isIntegerTy(64);
    if (!is_i32 && !is_i64) continue;
    if (is_i64 && !opts.vectorize_i64) continue;
    LaneContext &lc = is_i64 ? lc64 : lc32;

    // Materialise bitwise splats on first Add/Sub/Mul encounter, not upfront.
    if (opts.vectorize_bitwise &&
        (bin->getOpcode() == llvm::Instruction::Add ||
         bin->getOpcode() == llvm::Instruction::Sub ||
         bin->getOpcode() == llvm::Instruction::Mul)) {
      lc.ensureBitwiseSplats(entry_builder);
    }

    // Clear the scalar→vector cache at the start of each iteration so
    // stale entries from a previous iteration that was rejected by a guard
    // (type, cross-function) don't leak across basic blocks.
    lc.scalar_to_vector.clear();

    llvm::IRBuilder<> builder(bin);
    auto *a = bin->getOperand(0);
    auto *b = bin->getOperand(1);

    // Skip non-integer operands (e.g. pointer values from flattening demotes).
    if (!a->getType()->isIntegerTy() || !b->getType()->isIntegerTy())
      continue;

    llvm::Value *va = nullptr;
    llvm::Value *vb = nullptr;
    if (auto *ca = llvm::dyn_cast<llvm::ConstantInt>(a)) {
      va = lc.getConstSplat(entry_builder, ca);
    } else {
      va = liftLane0ToVector(builder, a, lc, opts.vectorize_data, DT, bin);
    }
    if (auto *cb = llvm::dyn_cast<llvm::ConstantInt>(b)) {
      vb = lc.getConstSplat(entry_builder, cb);
    } else {
      vb = liftLane0ToVector(builder, b, lc, opts.vectorize_data, DT, bin);
    }


    // Final type guard.
    if (!va || !vb) continue;
    if (va->getType() != lc.vec_ty || vb->getType() != lc.vec_ty)
      continue;

    // Domination guard: both vector operands must dominate the insertion
    // point. DomTree handles cross-block queries correctly.
    auto dominatesInsert = [&DT, bin](llvm::Value *v) {
      if (auto *inst = llvm::dyn_cast<llvm::Instruction>(v))
        return DT.dominates(inst, bin);
      return true;  // constants always dominate
    };
    if (!dominatesInsert(va) || !dominatesInsert(vb))
      continue;

    auto *vr = buildVectorBinOp(builder, bin->getOpcode(), va, vb, opts, lc);

    auto *result = builder.CreateExtractElement(vr, lc.idx_zero);
    lc.created_extracts.push_back(
        llvm::cast<llvm::ExtractElementInst>(result));

    // Clear the cache before erasing — erased instruction memory may be
    // reused by the allocator, creating stale entries with colliding addresses.
    lc.scalar_to_vector.clear();
    bin->replaceAllUsesWith(result);
    bin->eraseFromParent();
  }

  // Drop now-unused lane-0 extracts created as temporary scalar adapters.
  lc32.cleanupDeadExtracts();
  if (opts.vectorize_i64)
    lc64.cleanupDeadExtracts();
}

}  // namespace

void vectorizeModule(llvm::Module &M, uint32_t seed,
                     const VectorizeOptions &opts,
                     const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    vectorizeFunction(F, rng, opts, cfg);
  }
}

}  // namespace ollvm
