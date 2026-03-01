#include "BogusControlFlow.h"
#include "PassFilter.h"
#include "OpaquePredicateLib.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Transforms/Utils/ValueMapper.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Determine whether a basic block is eligible for BCF.
/// The block must end with an unconditional branch (not entry, not return,
/// not invoke/resume, not trivial).
static bool isEligibleBlock(llvm::BasicBlock &BB) {
  if (&BB == &BB.getParent()->getEntryBlock())
    return false;
  if (BB.size() <= 1)
    return false;

  auto *term = BB.getTerminator();
  auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
  if (!br || !br->isUnconditional())
    return false;

  return true;
}

/// Mutate a cloned instruction to look structurally different.
static void mutateClonedInstruction(llvm::Instruction *I,
                                    std::mt19937 &rng) {
  if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(I)) {
    std::uniform_int_distribution<int> coin(0, 1);
    if (coin(rng) == 0)
      return;

    if (bin->getOpcode() == llvm::Instruction::Add) {
      auto *newBin = llvm::BinaryOperator::Create(
          llvm::Instruction::Sub, bin->getOperand(0), bin->getOperand(1),
          bin->getName(), bin->getIterator());
      bin->replaceAllUsesWith(newBin);
      bin->eraseFromParent();
    } else if (bin->getOpcode() == llvm::Instruction::Sub) {
      auto *newBin = llvm::BinaryOperator::Create(
          llvm::Instruction::Add, bin->getOperand(0), bin->getOperand(1),
          bin->getName(), bin->getIterator());
      bin->replaceAllUsesWith(newBin);
      bin->eraseFromParent();
    }
    return;
  }

  // Skip instructions where mutating constants would create invalid IR:
  // GEPs (struct indices), calls (intrinsic IDs), switches, etc.
  if (llvm::isa<llvm::GetElementPtrInst>(I) ||
      llvm::isa<llvm::CallBase>(I) ||
      llvm::isa<llvm::SwitchInst>(I) ||
      llvm::isa<llvm::ExtractValueInst>(I) ||
      llvm::isa<llvm::InsertValueInst>(I))
    return;

  for (unsigned i = 0, e = I->getNumOperands(); i < e; ++i) {
    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(I->getOperand(i))) {
      if (ci->getBitWidth() >= 8 && !ci->isZero()) {
        std::uniform_int_distribution<int> delta(1, 3);
        auto newVal = ci->getValue() + delta(rng);
        I->setOperand(i, llvm::ConstantInt::get(ci->getType(), newVal));
        break;
      }
    }
  }
}

/// Create a junk (bogus) block that references real program values,
/// making it harder to distinguish from live code via static analysis.
static llvm::BasicBlock *createJunkBlock(llvm::Function &F,
                                         llvm::BasicBlock *target,
                                         std::mt19937 &rng,
                                         llvm::AllocaInst *sinkAlloca) {
  auto &ctx = F.getContext();
  auto *i64Ty = llvm::Type::getInt64Ty(ctx);
  auto *junkBB = llvm::BasicBlock::Create(ctx, "", &F);
  llvm::IRBuilder<> builder(junkBB);

  // Collect source values: function args + feedback from sinkAlloca.
  std::vector<llvm::Value *> sources;

  // Load from sinkAlloca (creates feedback loop that looks like state).
  sources.push_back(builder.CreateLoad(i64Ty, sinkAlloca, ""));

  // Add function arguments as sources.
  for (auto &arg : F.args()) {
    if (arg.getType()->isIntegerTy()) {
      auto *ext = builder.CreateZExtOrTrunc(&arg, i64Ty, "");
      sources.push_back(ext);
    } else if (arg.getType()->isPointerTy()) {
      sources.push_back(builder.CreatePtrToInt(&arg, i64Ty, ""));
    }
  }

  // If only the sinkAlloca load is available (no args), add constants
  // so we still get non-trivial arithmetic.
  if (sources.size() < 2) {
    std::uniform_int_distribution<uint64_t> cDist(1, 0xFFFFFFFF);
    sources.push_back(llvm::ConstantInt::get(i64Ty, cDist(rng)));
    sources.push_back(llvm::ConstantInt::get(i64Ty, cDist(rng)));
  }

  // Generate 3-6 random arithmetic operations chaining source values.
  std::uniform_int_distribution<int> opCountDist(3, 6);
  std::uniform_int_distribution<int> opKindDist(0, 5);
  int opCount = opCountDist(rng);

  auto pickSource = [&](std::mt19937 &r) -> llvm::Value * {
    std::uniform_int_distribution<size_t> idx(0, sources.size() - 1);
    return sources[idx(r)];
  };

  llvm::Value *acc = pickSource(rng);
  for (int i = 0; i < opCount; ++i) {
    llvm::Value *operand = pickSource(rng);
    switch (opKindDist(rng)) {
    case 0: acc = builder.CreateAdd(acc, operand, ""); break;
    case 1: acc = builder.CreateSub(acc, operand, ""); break;
    case 2: acc = builder.CreateXor(acc, operand, ""); break;
    case 3: acc = builder.CreateMul(acc, operand, ""); break;
    case 4: acc = builder.CreateAnd(acc, operand, ""); break;
    case 5: acc = builder.CreateOr(acc, operand, ""); break;
    }
  }

  // Store final result to sinkAlloca (makes computation look live).
  builder.CreateStore(acc, sinkAlloca);

  // Branch unconditionally to the real target.
  builder.CreateBr(target);
  return junkBB;
}

static void insertBogusControlFlowFunction(llvm::Function &F,
                                           std::mt19937 &rng,
                                           const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg) || F.size() <= 1)
    return;

  std::vector<llvm::BasicBlock *> candidates;
  for (auto &BB : F) {
    if (isEligibleBlock(BB))
      candidates.push_back(&BB);
  }

  if (candidates.empty())
    return;

  // Select ~30% of eligible blocks.
  std::uniform_int_distribution<int> percent(0, 99);
  std::vector<llvm::BasicBlock *> selected;
  for (auto *BB : candidates) {
    if (shouldTransform(rng, cfg) && percent(rng) < 30)
      selected.push_back(BB);
  }

  if (selected.empty())
    return;

  // Obtain an integer value for the opaque predicate.
  auto &ctx = F.getContext();
  auto *i32Ty = llvm::Type::getInt32Ty(ctx);
  llvm::Value *opaqueInput = nullptr;

  if (!F.arg_empty()) {
    for (auto &arg : F.args()) {
      if (arg.getType()->isIntegerTy()) {
        opaqueInput = &arg;
        break;
      }
    }
    if (!opaqueInput) {
      // Try pointer args — PtrToInt only valid on pointer types.
      for (auto &arg : F.args()) {
        if (arg.getType()->isPointerTy()) {
          auto &entry = F.getEntryBlock();
          llvm::IRBuilder<> entryBuilder(&entry,
                                         entry.getFirstInsertionPt());
          opaqueInput = entryBuilder.CreatePtrToInt(&arg, i32Ty);
          break;
        }
      }
    }
    if (!opaqueInput) {
      // No integer or pointer args — fall back to global variable.
      auto *M = F.getParent();
      auto *gv = new llvm::GlobalVariable(
          *M, i32Ty, /*isConstant=*/false,
          llvm::GlobalValue::PrivateLinkage,
          llvm::ConstantInt::get(i32Ty, 0));
      auto &entry = F.getEntryBlock();
      llvm::IRBuilder<> entryBuilder(&entry, entry.getFirstInsertionPt());
      opaqueInput = entryBuilder.CreateLoad(i32Ty, gv,
                                             /*isVolatile=*/true);
    }
  } else {
    auto *M = F.getParent();
    auto *gv = new llvm::GlobalVariable(
        *M, i32Ty, /*isConstant=*/false, llvm::GlobalValue::PrivateLinkage,
        llvm::ConstantInt::get(i32Ty, 0));
    auto &entry = F.getEntryBlock();
    llvm::IRBuilder<> entryBuilder(&entry, entry.getFirstInsertionPt());
    auto *load = entryBuilder.CreateLoad(i32Ty, gv, /*isVolatile=*/true);
    opaqueInput = load;
  }

  // Strategy: for each selected block ending with `br successor`:
  //   1. Create a junk block with correlated arithmetic referencing
  //      real function arguments and a persistent sink alloca.
  //   2. Replace origBB's unconditional `br successor` with
  //      `br opaque_true, successor, junkBB`.
  //   3. Update PHI nodes in successor for the new junkBB predecessor.
  //
  // This preserves domination since origBB is never moved or split.

  // Create a sink alloca in the entry block for junk block state.
  auto *i64Ty = llvm::Type::getInt64Ty(ctx);
  auto &entryBB = F.getEntryBlock();
  llvm::IRBuilder<> allocaBuilder(&entryBB, entryBB.getFirstInsertionPt());
  auto *sinkAlloca = allocaBuilder.CreateAlloca(i64Ty, nullptr, "");
  allocaBuilder.CreateStore(llvm::ConstantInt::get(i64Ty, 0), sinkAlloca);

  for (auto *origBB : selected) {
    auto *br = llvm::cast<llvm::BranchInst>(origBB->getTerminator());
    auto *successor = br->getSuccessor(0);

    // Create the junk (bogus) block with correlated values.
    auto *junkBB = createJunkBlock(F, successor, rng, sinkAlloca);

    // Update PHI nodes in successor: junkBB is a new predecessor.
    // Use undef since the junk path is always dead.
    for (auto &inst : *successor) {
      auto *phi = llvm::dyn_cast<llvm::PHINode>(&inst);
      if (!phi) break;
      phi->addIncoming(llvm::UndefValue::get(phi->getType()), junkBB);
    }

    // Replace origBB's unconditional branch with conditional.
    // Randomly flip polarity: ~50% true-branch-is-real, ~50% false-branch-is-real.
    llvm::IRBuilder<> builder(br);
    std::uniform_int_distribution<int> flipDist(0, 1);
    bool flip = flipDist(rng);
    auto *cond = flip
        ? ollvm::generateOpaqueFalse(builder, opaqueInput, rng())
        : ollvm::generateOpaqueTrue(builder, opaqueInput, rng());
    br->eraseFromParent();
    if (flip)
      llvm::BranchInst::Create(junkBB, successor, cond, origBB);
    else
      llvm::BranchInst::Create(successor, junkBB, cond, origBB);
  }
}

void insertBogusControlFlowModule(llvm::Module &M, uint32_t seed,
                                  const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    insertBogusControlFlowFunction(F, rng, cfg);
  }
}

}  // namespace ollvm
