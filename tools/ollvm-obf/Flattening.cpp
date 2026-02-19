#include "Flattening.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Merge basic block chains where A → B unconditionally and B has only one
/// predecessor. This ensures each block is self-contained before flattening.
static void mergeLinearChains(llvm::Function &F) {
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &BB : F) {
      auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
      if (!br || !br->isUnconditional())
        continue;
      auto *succ = br->getSuccessor(0);
      if (succ == &BB)
        continue;
      if (succ->hasNPredecessorsOrMore(2))
        continue;
      if (!succ->hasNPredecessorsOrMore(1))
        continue;
      br->eraseFromParent();
      while (auto *phi = llvm::dyn_cast<llvm::PHINode>(&succ->front())) {
        phi->replaceAllUsesWith(phi->getIncomingValue(0));
        phi->eraseFromParent();
      }
      BB.splice(BB.end(), succ);
      succ->eraseFromParent();
      changed = true;
      break;
    }
  }
}

/// Demote all PHI nodes in the function to alloca/store/load sequences.
/// This is necessary before CFF because the switch dispatcher breaks
/// the predecessor relationships that PHI nodes depend on.
static void demotePhiNodes(llvm::Function &F) {
  // Collect all PHI nodes.
  std::vector<llvm::PHINode *> phis;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *phi = llvm::dyn_cast<llvm::PHINode>(&I))
        phis.push_back(phi);
    }
  }

  if (phis.empty())
    return;

  // Insert allocas at the entry block.
  llvm::BasicBlock &entry = F.getEntryBlock();
  llvm::IRBuilder<> alloca_builder(&entry, entry.begin());

  for (auto *phi : phis) {
    auto *alloca =
        alloca_builder.CreateAlloca(phi->getType(), nullptr, "phi_demote");

    // Insert stores in each predecessor block.
    for (unsigned i = 0, e = phi->getNumIncomingValues(); i < e; ++i) {
      auto *pred = phi->getIncomingBlock(i);
      auto *val = phi->getIncomingValue(i);
      // Insert store before the terminator of the predecessor.
      llvm::IRBuilder<> store_builder(pred->getTerminator());
      store_builder.CreateStore(val, alloca);
    }

    // Replace PHI with a load after the PHI's position.
    llvm::IRBuilder<> load_builder(phi->getParent(),
                                   phi->getParent()->getFirstNonPHIIt());
    auto *load = load_builder.CreateLoad(phi->getType(), alloca, "phi_load");
    phi->replaceAllUsesWith(load);
    phi->eraseFromParent();
  }
}

/// Demote all instructions with cross-block uses to alloca/store/load.
/// After CFF, no switch case dominates another, so any value defined in one
/// block and used in another causes a domination failure.
static void demoteCrossBlockValues(llvm::Function &F) {
  llvm::BasicBlock &entry = F.getEntryBlock();
  llvm::IRBuilder<> alloca_builder(&entry, entry.begin());

  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &BB : F) {
      for (auto it = BB.begin(); it != BB.end(); ++it) {
        auto *I = &*it;
        // Skip allocas, terminators, and void-typed instructions.
        if (llvm::isa<llvm::AllocaInst>(I) || I->isTerminator() ||
            I->getType()->isVoidTy())
          continue;

        // Check if any use is in a different block.
        bool has_cross_block_use = false;
        for (auto *user : I->users()) {
          if (auto *user_inst = llvm::dyn_cast<llvm::Instruction>(user)) {
            if (user_inst->getParent() != &BB) {
              has_cross_block_use = true;
              break;
            }
          }
        }
        if (!has_cross_block_use)
          continue;

        // Demote to alloca.
        auto *alloca = alloca_builder.CreateAlloca(
            I->getType(), nullptr, I->getName() + ".demote");

        // Store after the instruction.
        llvm::IRBuilder<> store_builder(I->getNextNode());
        store_builder.CreateStore(I, alloca);

        // Replace cross-block uses with loads.
        std::vector<llvm::Use *> cross_uses;
        for (auto &U : I->uses()) {
          if (auto *user_inst = llvm::dyn_cast<llvm::Instruction>(U.getUser())) {
            if (user_inst->getParent() != &BB)
              cross_uses.push_back(&U);
          }
        }

        for (auto *U : cross_uses) {
          auto *user_inst = llvm::cast<llvm::Instruction>(U->getUser());
          llvm::IRBuilder<> load_builder(user_inst);
          auto *load = load_builder.CreateLoad(I->getType(), alloca,
                                               I->getName() + ".reload");
          U->set(load);
        }

        changed = true;
        break;  // restart scan since we modified uses
      }
      if (changed)
        break;
    }
  }
}

static void flattenFunction(llvm::Function &F, std::mt19937 &rng) {
  if (F.isDeclaration() || F.size() <= 1)
    return;

  // Step 1: Merge linear chains.
  mergeLinearChains(F);

  if (F.size() <= 1)
    return;

  // Step 2: Demote PHI nodes to allocas (CFF breaks PHI predecessor info),
  // then demote all cross-block SSA values (CFF switch cases don't dominate
  // each other).
  demotePhiNodes(F);
  demoteCrossBlockValues(F);

  // Collect all basic blocks except entry.
  llvm::BasicBlock &entry = F.getEntryBlock();
  std::vector<llvm::BasicBlock *> orig_bbs;
  for (auto &BB : F) {
    if (&BB != &entry)
      orig_bbs.push_back(&BB);
  }
  if (orig_bbs.empty())
    return;

  // Assign random case IDs to each basic block.
  std::uniform_int_distribution<uint32_t> dist(1, 0x7FFFFFFE);
  llvm::DenseSet<uint32_t> used_ids;
  llvm::DenseMap<llvm::BasicBlock *, uint32_t> bb_to_case;
  for (auto *BB : orig_bbs) {
    uint32_t id;
    do {
      id = dist(rng);
    } while (used_ids.count(id));
    used_ids.insert(id);
    bb_to_case[BB] = id;
  }

  uint32_t initial_case = bb_to_case[orig_bbs[0]];

  auto &ctx = F.getContext();
  auto *i32_ty = llvm::Type::getInt32Ty(ctx);

  // Split the entry block: move non-alloca instructions into a new block.
  llvm::Instruction *split_pt = nullptr;
  for (auto &I : entry) {
    if (!llvm::isa<llvm::AllocaInst>(&I)) {
      split_pt = &I;
      break;
    }
  }

  if (split_pt && split_pt != entry.getTerminator()) {
    auto *entry_tail = entry.splitBasicBlock(split_pt, "entry_tail");
    uint32_t tail_id;
    do {
      tail_id = dist(rng);
    } while (used_ids.count(tail_id));
    used_ids.insert(tail_id);
    bb_to_case[entry_tail] = tail_id;
    orig_bbs.insert(orig_bbs.begin(), entry_tail);
    initial_case = tail_id;
  }

  // Create switch variable alloca at the start of entry.
  llvm::IRBuilder<> entry_builder(&entry, entry.begin());
  auto *switch_var = entry_builder.CreateAlloca(i32_ty, nullptr, "switch_var");

  auto *entry_term = entry.getTerminator();

  // Create dispatcher and loop-back blocks.
  auto *dispatcher =
      llvm::BasicBlock::Create(ctx, "cff_dispatcher", &F, orig_bbs[0]);
  auto *loop_end =
      llvm::BasicBlock::Create(ctx, "cff_loop_end", &F);

  // Replace entry terminator.
  if (entry_term) {
    llvm::IRBuilder<> eb(entry_term);
    eb.CreateStore(llvm::ConstantInt::get(i32_ty, initial_case), switch_var);
    eb.CreateBr(dispatcher);
    for (unsigned i = 0, e = entry_term->getNumSuccessors(); i < e; ++i) {
      entry_term->getSuccessor(i)->removePredecessor(&entry);
    }
    entry_term->eraseFromParent();
  }

  // Build the switch in the dispatcher.
  llvm::IRBuilder<> disp_builder(dispatcher);
  auto *load = disp_builder.CreateLoad(i32_ty, switch_var, "cff_case");
  auto *default_bb =
      llvm::BasicBlock::Create(ctx, "cff_default", &F);
  llvm::IRBuilder<> def_builder(default_bb);
  // Store a defined value back to switch_var so that after mem2reg the
  // dispatcher's phi-node has a non-undef contribution from this predecessor.
  // Without this, LLVM's SCCP treats the phi as potentially-undef and may
  // prove all case blocks unreachable, collapsing the function to this loop.
  def_builder.CreateStore(llvm::ConstantInt::get(i32_ty, initial_case),
                          switch_var);
  // Prevent loop-deletion passes from removing this as a side-effect-free loop.
  def_builder.CreateCall(
      llvm::Intrinsic::getOrInsertDeclaration(F.getParent(),
                                              llvm::Intrinsic::sideeffect));
  def_builder.CreateBr(dispatcher);

  auto *sw =
      disp_builder.CreateSwitch(load, default_bb,
                                static_cast<unsigned>(orig_bbs.size()));

  for (auto *BB : orig_bbs) {
    sw->addCase(llvm::ConstantInt::get(i32_ty, bb_to_case[BB]), BB);
  }

  // loop_end: branch back to dispatcher.
  llvm::IRBuilder<> loop_builder(loop_end);
  loop_builder.CreateBr(dispatcher);

  // Rewrite each original block's terminator.
  for (auto *BB : orig_bbs) {
    auto *term = BB->getTerminator();
    if (!term)
      continue;

    if (auto *br = llvm::dyn_cast<llvm::BranchInst>(term)) {
      if (br->isUnconditional()) {
        auto *dest = br->getSuccessor(0);
        auto it = bb_to_case.find(dest);
        if (it != bb_to_case.end()) {
          llvm::IRBuilder<> builder(br);
          builder.CreateStore(llvm::ConstantInt::get(i32_ty, it->second),
                              switch_var);
          builder.CreateBr(loop_end);
          dest->removePredecessor(BB);
          br->eraseFromParent();
        }
      } else {
        auto *true_bb = br->getSuccessor(0);
        auto *false_bb = br->getSuccessor(1);
        auto *cond = br->getCondition();

        auto true_it = bb_to_case.find(true_bb);
        auto false_it = bb_to_case.find(false_bb);
        if (true_it != bb_to_case.end() && false_it != bb_to_case.end()) {
          llvm::IRBuilder<> builder(br);
          auto *true_val = llvm::ConstantInt::get(i32_ty, true_it->second);
          auto *false_val = llvm::ConstantInt::get(i32_ty, false_it->second);
          auto *sel = builder.CreateSelect(cond, true_val, false_val);
          builder.CreateStore(sel, switch_var);
          builder.CreateBr(loop_end);
          true_bb->removePredecessor(BB);
          false_bb->removePredecessor(BB);
          br->eraseFromParent();
        }
      }
    } else if (llvm::isa<llvm::ReturnInst>(term)) {
      // Return instructions stay as-is.
    }
    // Other terminators (switch, invoke, etc.) are left as-is.
  }
}

void flattenModule(llvm::Module &M, uint32_t seed) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    flattenFunction(F, rng);
  }
}

}  // namespace ollvm
