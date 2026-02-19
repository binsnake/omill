#include "Vectorize.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/IntrinsicInst.h>
#include <llvm/IR/Instructions.h>

#include <algorithm>
#include <random>
#include <vector>

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

llvm::Value *liftLane0ToVector(llvm::IRBuilder<> &builder, llvm::Value *v,
                               llvm::FixedVectorType *vec_ty,
                               llvm::Constant *zero_vec,
                               llvm::ConstantInt *idx_zero,
                               bool reuse_vector_data) {
  // Data-aware mode: if this scalar came from extractelement %vec, 0,
  // reuse the vector payload directly to keep data in vector space.
  if (reuse_vector_data) {
    if (auto *ee = llvm::dyn_cast<llvm::ExtractElementInst>(v)) {
      if (ee->getVectorOperand()->getType() == vec_ty && isZeroLane(ee->getIndexOperand()))
        return ee->getVectorOperand();
    }
  }

  return builder.CreateInsertElement(zero_vec, v, idx_zero);
}

llvm::Value *buildVectorBitwiseAdd(llvm::IRBuilder<> &builder,
                                   llvm::Value *lhs, llvm::Value *rhs,
                                   llvm::Constant *one_vec) {
  llvm::Value *sum = lhs;
  llvm::Value *carry = rhs;

  // Fixed 32-step ripple-carry adder over i32 lanes using vector bit ops.
  for (unsigned i = 0; i < 32; ++i) {
    auto *new_sum = builder.CreateXor(sum, carry);
    auto *new_carry = builder.CreateAnd(sum, carry);
    carry = builder.CreateShl(new_carry, one_vec);
    sum = new_sum;
  }
  return sum;
}

llvm::Value *buildVectorBinOp(llvm::IRBuilder<> &builder, unsigned opcode,
                              llvm::Value *va, llvm::Value *vb,
                              const VectorizeOptions &opts,
                              llvm::Constant *one_vec,
                              llvm::Constant *all_ones_vec) {
  if (!opts.vectorize_bitwise) {
    return builder.CreateBinOp(
        static_cast<llvm::Instruction::BinaryOps>(opcode), va, vb);
  }

  if (opcode == llvm::Instruction::Add) {
    return buildVectorBitwiseAdd(builder, va, vb, one_vec);
  }

  if (opcode == llvm::Instruction::Sub) {
    // a - b == a + (~b + 1) using vector bitwise adder.
    auto *not_b = builder.CreateXor(vb, all_ones_vec);
    auto *twos_complement_b = buildVectorBitwiseAdd(builder, not_b, one_vec, one_vec);
    return buildVectorBitwiseAdd(builder, va, twos_complement_b, one_vec);
  }

  return builder.CreateBinOp(
      static_cast<llvm::Instruction::BinaryOps>(opcode), va, vb);
}

void vectorizeI32StackData(llvm::Function &F, llvm::FixedVectorType *vec_ty,
                           llvm::Constant *zero_vec,
                           llvm::ConstantInt *idx_zero) {
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
    if (!alloca->getAllocatedType()->isIntegerTy(32))
      continue;

    bool supported = true;
    for (llvm::User *U : alloca->users()) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(U)) {
        if (LI->isVolatile() || LI->isAtomic() || LI->getPointerOperand() != alloca) {
          supported = false;
          break;
        }
        continue;
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
        if (SI->isVolatile() || SI->isAtomic() || SI->getPointerOperand() != alloca ||
            !SI->getValueOperand()->getType()->isIntegerTy(32)) {
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

  for (auto *alloca : candidates) {
    llvm::Instruction *insert_pt = alloca->getNextNode();
    if (!insert_pt)
      insert_pt = entry.getTerminator();

    llvm::IRBuilder<> alloca_builder(insert_pt);
    auto *vec_alloca =
        alloca_builder.CreateAlloca(vec_ty, nullptr, alloca->getName() + ".vec");
    vec_alloca->setAlignment(alloca->getAlign());

    llvm::SmallVector<llvm::Instruction *, 16> users;
    for (llvm::User *U : alloca->users()) {
      if (auto *I = llvm::dyn_cast<llvm::Instruction>(U))
        users.push_back(I);
    }

    for (auto *U : users) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(U)) {
        llvm::IRBuilder<> b(LI);
        auto *vload = b.CreateLoad(vec_ty, vec_alloca, LI->getName() + ".v");
        vload->setAlignment(LI->getAlign());
        auto *lane0 = b.CreateExtractElement(vload, idx_zero, LI->getName() + ".lane0");
        LI->replaceAllUsesWith(lane0);
        LI->eraseFromParent();
        continue;
      }

      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(U)) {
        llvm::IRBuilder<> b(SI);
        auto *packed = b.CreateInsertElement(zero_vec, SI->getValueOperand(), idx_zero);
        auto *vstore = b.CreateStore(packed, vec_alloca);
        vstore->setAlignment(SI->getAlign());
        SI->eraseFromParent();
      }
    }
  }
}

void vectorizeFunction(llvm::Function &F, std::mt19937 &rng,
                       const VectorizeOptions &opts) {
  if (F.isDeclaration())
    return;

  std::uniform_int_distribution<int> percent(0, 99);

  // Collect eligible instructions.
  std::vector<llvm::BinaryOperator *> work;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!bin)
        continue;
      // Only i32 for clean SSE2 mapping.
      if (!bin->getType()->isIntegerTy(32))
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

  auto &ctx = F.getContext();
  auto *vec_ty = llvm::FixedVectorType::get(llvm::Type::getInt32Ty(ctx), 4);
  auto *i32_ty = llvm::Type::getInt32Ty(ctx);
  auto *zero_vec = llvm::ConstantAggregateZero::get(vec_ty);
  auto *one_vec = llvm::ConstantVector::getSplat(
      llvm::ElementCount::getFixed(4), llvm::ConstantInt::get(i32_ty, 1));
  auto *all_ones_vec = llvm::ConstantVector::getSplat(
      llvm::ElementCount::getFixed(4), llvm::ConstantInt::getSigned(i32_ty, -1));
  auto *idx_zero = llvm::ConstantInt::get(i32_ty, 0);

  if (opts.vectorize_data) {
    vectorizeI32StackData(F, vec_ty, zero_vec, idx_zero);
  }

  const unsigned threshold = std::min(opts.transform_percent, 100u);

  for (auto *bin : work) {
    // Apply to configured percent of eligible ops.
    if (threshold == 0 || percent(rng) >= static_cast<int>(threshold))
      continue;

    llvm::IRBuilder<> builder(bin);
    auto *a = bin->getOperand(0);
    auto *b = bin->getOperand(1);

    auto *va = liftLane0ToVector(builder, a, vec_ty, zero_vec, idx_zero,
                                 opts.vectorize_data);
    auto *vb = liftLane0ToVector(builder, b, vec_ty, zero_vec, idx_zero,
                                 opts.vectorize_data);
    auto *vr = buildVectorBinOp(builder, bin->getOpcode(), va, vb, opts,
                                one_vec, all_ones_vec);

    auto *result = builder.CreateExtractElement(vr, idx_zero);

    bin->replaceAllUsesWith(result);
    bin->eraseFromParent();
  }
}

}  // namespace

void vectorizeModule(llvm::Module &M, uint32_t seed,
                     const VectorizeOptions &opts) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    vectorizeFunction(F, rng, opts);
  }
}

}  // namespace ollvm
