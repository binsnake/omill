#include "Vectorize.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

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

void vectorizeFunction(llvm::Function &F, std::mt19937 &rng) {
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
  auto *vec_ty = llvm::FixedVectorType::get(
      llvm::Type::getInt32Ty(ctx), 4);
  auto *i32_ty = llvm::Type::getInt32Ty(ctx);
  auto *zero_vec = llvm::ConstantAggregateZero::get(vec_ty);
  auto *idx_zero = llvm::ConstantInt::get(i32_ty, 0);

  for (auto *bin : work) {
    // Apply to ~40% of eligible ops.
    if (percent(rng) >= 40)
      continue;

    llvm::IRBuilder<> builder(bin);
    auto *a = bin->getOperand(0);
    auto *b = bin->getOperand(1);

    // insertelement <4 x i32> zeroinitializer, i32 %a, i32 0
    auto *va = builder.CreateInsertElement(zero_vec, a, idx_zero);
    auto *vb = builder.CreateInsertElement(zero_vec, b, idx_zero);

    // Vector binary op with same opcode.
    auto *vr = builder.CreateBinOp(
        static_cast<llvm::Instruction::BinaryOps>(bin->getOpcode()), va, vb);

    // extractelement <4 x i32> %vr, i32 0
    auto *result = builder.CreateExtractElement(vr, idx_zero);

    bin->replaceAllUsesWith(result);
    bin->eraseFromParent();
  }
}

}  // namespace

void vectorizeModule(llvm::Module &M) {
  std::mt19937 rng(789);
  for (auto &F : M) {
    vectorizeFunction(F, rng);
  }
}

}  // namespace ollvm
