#include "Flattening.h"
#include "PassFilter.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/ArrayRef.h>
#include <llvm/ADT/SmallPtrSet.h>

#include <cstdint>
#include <random>
#include <vector>

namespace ollvm {

/// Compute modular inverse of an odd number mod 2^32 using Newton's method.
static uint32_t modInverse(uint32_t a) {
  // Newton iteration: x = x * (2 - a*x), converges in 5 steps for 32-bit
  uint32_t x = a;
  for (int i = 0; i < 5; ++i)
    x *= 2 - a * x;
  return x;
}

/// Merge basic block chains where A → B unconditionally and B has only one
/// predecessor. This ensures each block is self-contained before flattening.
static void mergeLinearChains(llvm::Function &F) {
  bool changed = true;
  while (changed) {
    changed = false;
    llvm::SmallVector<llvm::BasicBlock *, 16> mergeTargets;
    for (auto &BB : F) {
      auto *br = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
      if (!br || !br->isUnconditional())
        continue;
      auto *succ = br->getSuccessor(0);
      if (succ == &BB || succ == &F.getEntryBlock())
        continue;
      if (!succ->hasNPredecessors(1))
        continue;
      mergeTargets.push_back(&BB);
    }
    for (auto *BB : mergeTargets) {
      // Re-validate: earlier merges in this batch may have invalidated.
      auto *br = llvm::dyn_cast<llvm::BranchInst>(BB->getTerminator());
      if (!br || !br->isUnconditional())
        continue;
      auto *succ = br->getSuccessor(0);
      if (succ == BB || !succ->hasNPredecessors(1))
        continue;
      br->eraseFromParent();
      while (auto *phi = llvm::dyn_cast<llvm::PHINode>(&succ->front())) {
        phi->replaceAllUsesWith(phi->getIncomingValue(0));
        phi->eraseFromParent();
      }
      BB->splice(BB->end(), succ);
      succ->eraseFromParent();
      changed = true;
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
        alloca_builder.CreateAlloca(phi->getType(), nullptr, "");

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
    auto *load = load_builder.CreateLoad(phi->getType(), alloca, "");
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

  // Repeat until no cross-block uses remain. Demotion can introduce new
  // cross-block uses (loads placed in different blocks), but converges in
  // 2-3 iterations because each round strictly reduces the problem.
  while (true) {
    llvm::SmallVector<llvm::Instruction *, 32> worklist;
    for (auto &BB : F) {
      for (auto &I : BB) {
        if (llvm::isa<llvm::AllocaInst>(&I) || I.getType()->isVoidTy())
          continue;
        for (auto *user : I.users()) {
          if (auto *UI = llvm::dyn_cast<llvm::Instruction>(user)) {
            if (UI->getParent() != &BB) {
              worklist.push_back(&I);
              break;
            }
          }
        }
      }
    }

    if (worklist.empty())
      break;

    for (auto *I : worklist) {
      llvm::BasicBlock *defBB = I->getParent();
      bool is_terminator = I->isTerminator();

      auto *alloca = alloca_builder.CreateAlloca(
          I->getType(), nullptr, "");

      if (is_terminator) {
        if (auto *invoke = llvm::dyn_cast<llvm::InvokeInst>(I)) {
          auto *normalDest = invoke->getNormalDest();
          llvm::IRBuilder<> store_builder(
              &*normalDest->getFirstInsertionPt());
          store_builder.CreateStore(I, alloca);
        }
      } else {
        llvm::IRBuilder<> store_builder(I->getNextNode());
        store_builder.CreateStore(I, alloca);
      }

      std::vector<llvm::Use *> cross_uses;
      for (auto &U : I->uses()) {
        if (auto *user_inst =
                llvm::dyn_cast<llvm::Instruction>(U.getUser())) {
          if (user_inst->getParent() != defBB)
            cross_uses.push_back(&U);
        }
      }

      for (auto *U : cross_uses) {
        auto *user_inst = llvm::cast<llvm::Instruction>(U->getUser());
        if (auto *phi = llvm::dyn_cast<llvm::PHINode>(user_inst)) {
          for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
            if (phi->getIncomingValue(i) == I) {
              auto *incBB = phi->getIncomingBlock(i);
              llvm::IRBuilder<> load_builder(incBB->getTerminator());
              auto *load = load_builder.CreateLoad(
                  I->getType(), alloca, "");
              phi->setIncomingValue(i, load);
            }
          }
        } else {
          llvm::IRBuilder<> load_builder(user_inst);
          auto *load = load_builder.CreateLoad(I->getType(), alloca,
                                               "");
          U->set(load);
        }
      }
    }
  }
}

/// Check if a landing pad block is a simple "resume-only" pad that just
/// rethrows the exception without catch logic.
static bool isSimpleResumePad(llvm::BasicBlock *BB) {
  if (!BB->isLandingPad())
    return false;
  // A simple pad: landingpad instruction(s) followed by resume.
  // Allow extractvalue and other non-side-effecting intermediates.
  return llvm::isa<llvm::ResumeInst>(BB->getTerminator());
}

/// Convert invoke instructions whose unwind edge targets a simple
/// resume-only landing pad into call + unconditional branch.
/// Returns true if any conversions were made.
static bool simplifyTrivialInvokes(llvm::Function &F) {
  llvm::SmallVector<llvm::InvokeInst *, 4> toConvert;
  for (auto &BB : F) {
    if (auto *invoke = llvm::dyn_cast<llvm::InvokeInst>(BB.getTerminator())) {
      if (isSimpleResumePad(invoke->getUnwindDest()))
        toConvert.push_back(invoke);
    }
  }

  for (auto *invoke : toConvert) {
    auto *normalDest = invoke->getNormalDest();
    auto *unwindDest = invoke->getUnwindDest();
    auto *BB = invoke->getParent();

    // Build a call with identical operands and bundles.
    llvm::SmallVector<llvm::Value *, 8> args(invoke->args());
    llvm::SmallVector<llvm::OperandBundleDef, 2> bundles;
    invoke->getOperandBundlesAsDefs(bundles);
    auto *call = llvm::CallInst::Create(
        invoke->getFunctionType(), invoke->getCalledOperand(), args,
        bundles, invoke->getName(), invoke->getIterator());
    call->setCallingConv(invoke->getCallingConv());
    call->setAttributes(invoke->getAttributes());

    invoke->replaceAllUsesWith(call);

    // Detach this block from the unwind destination.
    unwindDest->removePredecessor(BB);

    // Replace the invoke terminator with an unconditional branch.
    llvm::BranchInst::Create(normalDest, invoke->getIterator());
    invoke->eraseFromParent();
  }

  return !toConvert.empty();
}

static void flattenFunction(llvm::Function &F, std::mt19937 &rng,
                            const FilterConfig &cfg) {
  if (shouldSkipFunction(F, cfg) || F.size() <= 1)
    return;
  if (!shouldTransform(rng, cfg)) return;

  // Step 0: Convert invokes with simple resume-only landing pads to
  // call + br. This lets us flatten blocks that were previously skipped.
  simplifyTrivialInvokes(F);

  // Step 1: Merge linear chains.
  mergeLinearChains(F);

  if (F.size() <= 1)
    return;

  // Identify EH infrastructure blocks that cannot go through the switch
  // dispatcher: EH pads (landing pads, catch pads, cleanup pads) and blocks
  // still terminated by invoke (which need their unwind edge intact).
  llvm::SmallPtrSet<llvm::BasicBlock *, 8> ehBlocks;
  for (auto &BB : F) {
    if (BB.isEHPad())
      ehBlocks.insert(&BB);
    if (llvm::isa<llvm::InvokeInst>(BB.getTerminator()))
      ehBlocks.insert(&BB);
  }

  // Step 2: Demote PHI nodes to allocas (CFF breaks PHI predecessor info),
  // then demote all cross-block SSA values (CFF switch cases don't dominate
  // each other).
  demotePhiNodes(F);
  demoteCrossBlockValues(F);

  // Step 2b: Hoist all fixed-size allocas in the entry block to the top.
  // mergeLinearChains may have spliced successor blocks into the entry,
  // interleaving their allocas with non-alloca instructions. The entry-block
  // split below would strand those allocas in entry_tail (a switch case that
  // does not dominate other cases), breaking domination.
  {
    llvm::BasicBlock &entry = F.getEntryBlock();
    llvm::SmallVector<llvm::AllocaInst *, 32> misplaced;
    bool seen_non_alloca = false;
    for (auto &I : entry) {
      if (auto *AI = llvm::dyn_cast<llvm::AllocaInst>(&I)) {
        if (seen_non_alloca &&
            llvm::isa<llvm::ConstantInt>(AI->getArraySize()))
          misplaced.push_back(AI);
      } else {
        seen_non_alloca = true;
      }
    }
    if (!misplaced.empty()) {
      llvm::Instruction *insertBefore = nullptr;
      for (auto &I : entry) {
        if (!llvm::isa<llvm::AllocaInst>(&I)) {
          insertBefore = &I;
          break;
        }
      }
      if (insertBefore) {
        for (auto *AI : misplaced)
          AI->moveBefore(insertBefore->getIterator());
      }
    }
  }

  // Collect all basic blocks except entry and EH blocks.
  llvm::BasicBlock &entry = F.getEntryBlock();
  std::vector<llvm::BasicBlock *> orig_bbs;
  for (auto &BB : F) {
    if (&BB != &entry && !ehBlocks.count(&BB))
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
    auto *entry_tail = entry.splitBasicBlock(split_pt, "");
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
  auto *switch_var = entry_builder.CreateAlloca(i32_ty, nullptr, "");

  auto *entry_term = entry.getTerminator();

  // Create dispatcher and loop-back blocks.
  auto *dispatcher =
      llvm::BasicBlock::Create(ctx, "", &F, orig_bbs[0]);
  auto *loop_end =
      llvm::BasicBlock::Create(ctx, "", &F);

  // Replace entry terminator.
  // Pick random odd multiplier A and addend B for affine encoding.
  // enc(id) = id * A + B,  dec(state) = (state - B) * A_inv
  uint32_t A;
  do {
    A = rng();
  } while ((A & 1) == 0);  // must be odd for invertibility mod 2^32
  uint32_t B = rng();
  uint32_t A_inv = modInverse(A);

  if (entry_term) {
    llvm::IRBuilder<> eb(entry_term);
    uint32_t enc_initial = initial_case * A + B;
    eb.CreateStore(llvm::ConstantInt::get(i32_ty, enc_initial), switch_var);
    eb.CreateBr(dispatcher);
    for (unsigned i = 0, e = entry_term->getNumSuccessors(); i < e; ++i) {
      entry_term->getSuccessor(i)->removePredecessor(&entry);
    }
    entry_term->eraseFromParent();
  }

  // Build the dispatch logic in the dispatcher block.
  llvm::IRBuilder<> disp_builder(dispatcher);
  auto *load_enc = disp_builder.CreateLoad(i32_ty, switch_var, "");
  // Decode: real_id = (load_enc - B) * A_inv
  auto *sub_b = disp_builder.CreateSub(
      load_enc, llvm::ConstantInt::get(i32_ty, B), "");
  auto *load = disp_builder.CreateMul(
      sub_b, llvm::ConstantInt::get(i32_ty, A_inv), "");
  auto *default_bb =
      llvm::BasicBlock::Create(ctx, "", &F);
  llvm::IRBuilder<> def_builder(default_bb);
  // Store a defined value back to switch_var so that after mem2reg the
  // dispatcher's phi-node has a non-undef contribution from this predecessor.
  // Without this, LLVM's SCCP treats the phi as potentially-undef and may
  // prove all case blocks unreachable, collapsing the function to this loop.
  {
    uint32_t enc_default = initial_case * A + B;
    def_builder.CreateStore(llvm::ConstantInt::get(i32_ty, enc_default),
                            switch_var);
  }
  // Prevent loop-deletion passes from removing this as a side-effect-free loop.
  // Use empty inline asm with side effects instead of @llvm.sideeffect intrinsic
  // to avoid leaving a fingerprintable intrinsic call.
  {
    auto *asmTy = llvm::FunctionType::get(llvm::Type::getVoidTy(ctx), false);
    auto *asmVal = llvm::InlineAsm::get(asmTy, "", "", /*hasSideEffects=*/true);
    def_builder.CreateCall(asmTy, asmVal);
  }
  def_builder.CreateBr(dispatcher);

  // Create bogus case blocks before dispatch so they can be included in
  // both switch and if-else dispatch variants.
  llvm::SmallVector<std::pair<uint32_t, llvm::BasicBlock *>, 16> all_cases;
  for (auto *BB : orig_bbs)
    all_cases.push_back({bb_to_case[BB], BB});

  {
    unsigned num_bogus = std::min<unsigned>(
        static_cast<unsigned>(orig_bbs.size()), 8u);
    if (num_bogus < 2)
      num_bogus = 2;
    for (unsigned bi = 0; bi < num_bogus; ++bi) {
      uint32_t bogus_id;
      do {
        bogus_id = dist(rng);
      } while (used_ids.count(bogus_id));
      used_ids.insert(bogus_id);

      auto *bogus_bb = llvm::BasicBlock::Create(ctx, "", &F);
      llvm::IRBuilder<> bb_builder(bogus_bb);
      auto *bogus_load = bb_builder.CreateLoad(i32_ty, switch_var, "");
      uint32_t xor_key = rng();
      auto *bogus_xor = bb_builder.CreateXor(
          bogus_load, llvm::ConstantInt::get(i32_ty, xor_key), "");
      bb_builder.CreateStore(bogus_xor, switch_var);
      bb_builder.CreateBr(loop_end);

      all_cases.push_back({bogus_id, bogus_bb});
    }
  }

  // Choose dispatch mode: ~50% switch, ~50% binary if-else tree.
  bool useIfElse = (rng() % 2 == 0);

  if (useIfElse) {
    // Sort cases by ID for balanced binary search.
    llvm::sort(all_cases, [](const auto &a, const auto &b) {
      return a.first < b.first;
    });

    // Build a balanced binary search tree of icmp+br.
    std::function<void(llvm::IRBuilder<> &, llvm::Value *,
                       llvm::ArrayRef<std::pair<uint32_t, llvm::BasicBlock *>>,
                       llvm::BasicBlock *)>
        buildTree;
    buildTree = [&](llvm::IRBuilder<> &builder, llvm::Value *val,
                    llvm::ArrayRef<std::pair<uint32_t, llvm::BasicBlock *>> cases,
                    llvm::BasicBlock *fallthrough) {
      if (cases.size() == 1) {
        auto *cmp = builder.CreateICmpEQ(
            val, llvm::ConstantInt::get(i32_ty, cases[0].first), "");
        builder.CreateCondBr(cmp, cases[0].second, fallthrough);
        return;
      }
      if (cases.size() == 2) {
        auto *elseBB = llvm::BasicBlock::Create(ctx, "", &F);
        auto *cmp = builder.CreateICmpEQ(
            val, llvm::ConstantInt::get(i32_ty, cases[0].first), "");
        builder.CreateCondBr(cmp, cases[0].second, elseBB);
        llvm::IRBuilder<> elseBuilder(elseBB);
        auto *cmp2 = elseBuilder.CreateICmpEQ(
            val, llvm::ConstantInt::get(i32_ty, cases[1].first), "");
        elseBuilder.CreateCondBr(cmp2, cases[1].second, fallthrough);
        return;
      }
      size_t mid = cases.size() / 2;
      auto *leftBB = llvm::BasicBlock::Create(ctx, "", &F);
      auto *rightBB = llvm::BasicBlock::Create(ctx, "", &F);
      auto *cmp = builder.CreateICmpSLT(
          val, llvm::ConstantInt::get(i32_ty, cases[mid].first), "");
      builder.CreateCondBr(cmp, leftBB, rightBB);
      llvm::IRBuilder<> leftBuilder(leftBB);
      buildTree(leftBuilder, val, cases.slice(0, mid), fallthrough);
      llvm::IRBuilder<> rightBuilder(rightBB);
      buildTree(rightBuilder, val, cases.slice(mid), fallthrough);
    };
    buildTree(disp_builder, load, all_cases, default_bb);
  } else {
    auto *sw =
        disp_builder.CreateSwitch(load, default_bb,
                                  static_cast<unsigned>(all_cases.size()));
    for (auto &[case_id, case_bb] : all_cases)
      sw->addCase(llvm::ConstantInt::get(i32_ty, case_id), case_bb);
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
          uint32_t enc_val = it->second * A + B;
          builder.CreateStore(llvm::ConstantInt::get(i32_ty, enc_val),
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
          uint32_t enc_true = true_it->second * A + B;
          uint32_t enc_false = false_it->second * A + B;
          auto *true_val = llvm::ConstantInt::get(i32_ty, enc_true);
          auto *false_val = llvm::ConstantInt::get(i32_ty, enc_false);
          auto *sel = builder.CreateSelect(cond, true_val, false_val);
          builder.CreateStore(sel, switch_var);
          builder.CreateBr(loop_end);
          true_bb->removePredecessor(BB);
          false_bb->removePredecessor(BB);
          br->eraseFromParent();
        }
      }
    } else if (llvm::isa<llvm::ReturnInst>(term) ||
               llvm::isa<llvm::UnreachableInst>(term)) {
      // Return and unreachable instructions stay as-is.
    } else if (auto *sw = llvm::dyn_cast<llvm::SwitchInst>(term)) {
      // Convert switch to a chain of icmp+select that maps each case
      // value to the corresponding CFF case ID.
      auto *cond = sw->getCondition();
      auto *defaultDest = sw->getDefaultDest();
      auto def_it = bb_to_case.find(defaultDest);
      if (def_it == bb_to_case.end())
        continue;  // can't redirect default — leave as-is

      llvm::IRBuilder<> builder(sw);
      uint32_t enc_def = def_it->second * A + B;
      llvm::Value *result =
          llvm::ConstantInt::get(i32_ty, enc_def);

      bool all_found = true;
      for (auto &c : sw->cases()) {
        auto case_it = bb_to_case.find(c.getCaseSuccessor());
        if (case_it == bb_to_case.end()) {
          all_found = false;
          break;
        }
        auto *cmp = builder.CreateICmpEQ(cond, c.getCaseValue());
        uint32_t enc_case = case_it->second * A + B;
        result = builder.CreateSelect(
            cmp, llvm::ConstantInt::get(i32_ty, enc_case),
            result);
      }

      if (!all_found)
        continue;  // some successors not in case map

      builder.CreateStore(result, switch_var);
      builder.CreateBr(loop_end);

      // Remove predecessor from all switch successors.
      llvm::SmallPtrSet<llvm::BasicBlock *, 8> succs;
      succs.insert(defaultDest);
      for (auto &c : sw->cases())
        succs.insert(c.getCaseSuccessor());
      for (auto *s : succs)
        s->removePredecessor(BB);

      sw->eraseFromParent();
    }
    // Other terminators (indirectbr, etc.) are left as-is.
  }

  // Encrypt integer constants in original blocks using their encoded state.
  // For each eligible BinaryOperator with i32 ConstantInt operands, replace the
  // constant with: load(switch_var) XOR encrypted_constant.  switch_var holds
  // the ENCODED state (case_id * A + B), so the XOR key must use that value.
  std::uniform_int_distribution<int> encrypt_coin(0, 1);
  for (auto *BB : orig_bbs) {
    // Compute the encoded state that switch_var holds when this BB executes.
    auto case_it = bb_to_case.find(BB);
    if (case_it == bb_to_case.end()) continue;
    uint32_t enc_state = case_it->second * A + B;

    for (auto &I : llvm::make_early_inc_range(*BB)) {
      auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(&I);
      if (!bin) continue;

      // Only encrypt eligible arithmetic/logic binary ops.
      switch (bin->getOpcode()) {
      case llvm::Instruction::Add:
      case llvm::Instruction::Sub:
      case llvm::Instruction::Xor:
      case llvm::Instruction::And:
      case llvm::Instruction::Or:
      case llvm::Instruction::Mul:
      case llvm::Instruction::Shl:
      case llvm::Instruction::LShr:
      case llvm::Instruction::AShr:
        break;
      default:
        continue;
      }

      // Encrypt ~50% of eligible ops to avoid excessive bloat.
      if (encrypt_coin(rng) == 0) continue;

      for (unsigned op = 0; op < bin->getNumOperands(); ++op) {
        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(bin->getOperand(op));
        if (!ci || ci->getType() != i32_ty) continue;

        // encrypted_const = original_const ^ enc_state (the encoded switch_var)
        uint32_t enc = static_cast<uint32_t>(ci->getZExtValue()) ^ enc_state;
        // At runtime: load switch_var, xor with enc -> recovers original
        llvm::IRBuilder<> enc_builder(bin);
        auto *sv_load = enc_builder.CreateLoad(i32_ty, switch_var, "");
        auto *decrypted = enc_builder.CreateXor(
            sv_load, llvm::ConstantInt::get(i32_ty, enc), "");
        bin->setOperand(op, decrypted);
      }
    }
  }
}

void flattenModule(llvm::Module &M, uint32_t seed,
                   const FilterConfig &cfg) {
  std::mt19937 rng(seed);
  for (auto &F : M) {
    flattenFunction(F, rng, cfg);
  }
}

}  // namespace ollvm
