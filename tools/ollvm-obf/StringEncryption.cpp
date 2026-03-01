#include "StringEncryption.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>

#include <cstdint>
#include <random>
#include <string>
#include <vector>

namespace ollvm {

void encryptStringsModule(llvm::Module &M, uint32_t seed) {
  std::mt19937 rng(seed);

  auto &ctx = M.getContext();
  auto *i8_ty = llvm::Type::getInt8Ty(ctx);
  auto *i32_ty = llvm::Type::getInt32Ty(ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);

  // Collect string globals to encrypt.
  struct StringInfo {
    llvm::GlobalVariable *gv;
    std::string data;
  };
  std::vector<StringInfo> strings;

  for (auto &GV : M.globals()) {
    if (!GV.hasInitializer() || !GV.isConstant())
      continue;
    if (GV.getSection().size() > 0)
      continue;  // Skip section-annotated globals.

    auto *CDA = llvm::dyn_cast<llvm::ConstantDataArray>(GV.getInitializer());
    if (!CDA || !CDA->isString())
      continue;

    llvm::StringRef raw = CDA->getAsString();
    if (raw.size() <= 4)
      continue;  // Skip tiny strings.

    // Must have null terminator.
    if (raw.back() != '\0')
      continue;

    strings.push_back({&GV, raw.str()});
  }

  for (auto &info : strings) {
    uint32_t key = rng();
    if (key == 0) key = 1;  // Avoid degenerate zero key.
    size_t len = info.data.size();

    // Encrypt with rolling feedback cipher.
    // state = (uint8_t)(key & 0xFF)
    // for each byte: enc[i] = data[i] ^ state;
    //                state = (state*31 + 17 + enc[i]) & 0xFF
    std::vector<uint8_t> encrypted(len);
    uint8_t state = static_cast<uint8_t>(key & 0xFF);
    for (size_t i = 0; i < len; ++i) {
      encrypted[i] = static_cast<uint8_t>(info.data[i]) ^ state;
      state = static_cast<uint8_t>((state * 31 + 17 + encrypted[i]) & 0xFF);
    }

    // Create encrypted data global (no name).
    auto *enc_data = llvm::ConstantDataArray::get(
        ctx, llvm::ArrayRef<uint8_t>(encrypted));
    auto *enc_gv = new llvm::GlobalVariable(
        M, enc_data->getType(), true, llvm::GlobalValue::PrivateLinkage,
        enc_data, "");

    // Create per-string i32 key global (no name).
    auto *key_val = llvm::ConstantInt::get(i32_ty, key);
    auto *key_gv = new llvm::GlobalVariable(
        M, i32_ty, true, llvm::GlobalValue::PrivateLinkage, key_val, "");

    auto *arr_ty = llvm::ArrayType::get(i8_ty, len);

    // Group uses by function.  A ConstantExpr user may be referenced from
    // multiple functions — record each instruction-level use site separately.
    struct UseSite {
      llvm::Use *string_use;       // Use in GV's use list (null for CE path).
      llvm::Instruction *inst;     // Instruction that transitively uses GV.
      llvm::ConstantExpr *via_ce;  // Non-null if use is through a ConstantExpr.
    };
    llvm::DenseMap<llvm::Function *, llvm::SmallVector<UseSite, 4>> func_uses;

    for (auto &U : info.gv->uses()) {
      auto *user = U.getUser();
      if (auto *inst = llvm::dyn_cast<llvm::Instruction>(user)) {
        auto *F = inst->getFunction();
        if (F)
          func_uses[F].push_back({&U, inst, nullptr});
      } else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(user)) {
        for (auto &CEU : ce->uses()) {
          if (auto *inst =
                  llvm::dyn_cast<llvm::Instruction>(CEU.getUser())) {
            auto *F = inst->getFunction();
            if (F)
              func_uses[F].push_back({nullptr, inst, ce});
          }
        }
      }
    }

    for (auto &[F, sites] : func_uses) {
      // One decryption buffer per (string, function) pair.
      llvm::BasicBlock &entry = F->getEntryBlock();
      llvm::IRBuilder<> alloca_builder(&*entry.getFirstInsertionPt());
      auto *buf = alloca_builder.CreateAlloca(arr_ty, nullptr, "");

      // Find insertion point after all allocas.
      llvm::Instruction *after_allocas = &*entry.getFirstInsertionPt();
      while (after_allocas && llvm::isa<llvm::AllocaInst>(after_allocas))
        after_allocas = after_allocas->getNextNode();
      if (!after_allocas)
        after_allocas = entry.getTerminator();

      llvm::IRBuilder<> builder(after_allocas);

      // Load the i32 key and truncate to i8 for initial state.
      auto *key_load = builder.CreateLoad(i32_ty, key_gv, "");
      auto *state_init = builder.CreateTrunc(key_load, i8_ty, "");

      auto *c31 = llvm::ConstantInt::get(i8_ty, 31);
      auto *c17 = llvm::ConstantInt::get(i8_ty, 17);

      if (len <= 32) {
        // Unrolled decryption with feedback.
        llvm::Value *cur_state = state_init;
        for (size_t i = 0; i < len; ++i) {
          auto *gep_enc = builder.CreateConstInBoundsGEP2_32(
              enc_data->getType(), enc_gv, 0, static_cast<unsigned>(i), "");
          auto *enc_byte = builder.CreateLoad(i8_ty, gep_enc, "");
          auto *dec_byte = builder.CreateXor(enc_byte, cur_state, "");
          auto *gep_buf = builder.CreateConstInBoundsGEP2_32(
              arr_ty, buf, 0, static_cast<unsigned>(i), "");
          builder.CreateStore(dec_byte, gep_buf);
          // state = (state * 31 + 17 + enc_byte) & 0xFF
          // The & 0xFF is implicit since we're using i8.
          auto *mul = builder.CreateMul(cur_state, c31, "");
          auto *add1 = builder.CreateAdd(mul, c17, "");
          cur_state = builder.CreateAdd(add1, enc_byte, "");
        }
      } else {
        // Loop-based decryption for larger strings.
        llvm::BasicBlock *preheader = builder.GetInsertBlock();

        // Split the current block: everything after our insertion goes to exit.
        // splitBasicBlock correctly updates PHI incoming blocks in successors.
        llvm::BasicBlock *exit_bb =
            preheader->splitBasicBlock(builder.GetInsertPoint(), "");

        // Create loop block between preheader and exit.
        llvm::BasicBlock *loop_bb =
            llvm::BasicBlock::Create(ctx, "", F, exit_bb);

        // Fix preheader terminator: branch to loop instead of exit.
        preheader->getTerminator()->eraseFromParent();
        llvm::IRBuilder<> pre_builder(preheader);
        pre_builder.CreateBr(loop_bb);

        // Build the loop.
        llvm::IRBuilder<> loop_builder(loop_bb);

        // PHI for index (i64).
        auto *phi_idx = loop_builder.CreatePHI(i64_ty, 2, "");
        phi_idx->addIncoming(llvm::ConstantInt::get(i64_ty, 0), preheader);

        // PHI for state (i8).
        auto *phi_state = loop_builder.CreatePHI(i8_ty, 2, "");
        phi_state->addIncoming(state_init, preheader);

        // Load enc_gv[i].
        llvm::Value *idx_vals[] = {
            llvm::ConstantInt::get(i64_ty, 0), phi_idx};
        auto *gep_enc = loop_builder.CreateInBoundsGEP(
            enc_data->getType(), enc_gv, idx_vals, "");
        auto *enc_byte = loop_builder.CreateLoad(i8_ty, gep_enc, "");

        // dec = enc ^ state
        auto *dec_byte = loop_builder.CreateXor(enc_byte, phi_state, "");

        // Store to buf[i].
        llvm::Value *buf_idx_vals[] = {
            llvm::ConstantInt::get(i64_ty, 0), phi_idx};
        auto *gep_buf = loop_builder.CreateInBoundsGEP(
            arr_ty, buf, buf_idx_vals, "");
        loop_builder.CreateStore(dec_byte, gep_buf);

        // new_state = state * 31 + 17 + enc_byte
        auto *mul = loop_builder.CreateMul(phi_state, c31, "");
        auto *add1 = loop_builder.CreateAdd(mul, c17, "");
        auto *new_state = loop_builder.CreateAdd(add1, enc_byte, "");

        // i_next = i + 1
        auto *i_next = loop_builder.CreateAdd(
            phi_idx, llvm::ConstantInt::get(i64_ty, 1), "");

        // Complete PHIs.
        phi_idx->addIncoming(i_next, loop_bb);
        phi_state->addIncoming(new_state, loop_bb);

        // Branch: if i_next < len goto loop, else goto exit.
        auto *cmp = loop_builder.CreateICmpULT(
            i_next, llvm::ConstantInt::get(i64_ty, len), "");
        loop_builder.CreateCondBr(cmp, loop_bb, exit_bb);

        // Continue building in exit_bb.
        builder.SetInsertPoint(&*exit_bb->getFirstInsertionPt());
      }

      // Create buf_ptr ONCE after decryption.  Since it's in the entry block
      // (unrolled case) or exit_bb (loop case), it dominates all original code
      // — including PHI predecessors.  This avoids the old bug of inserting a
      // GEP at each use site, which could place a non-PHI instruction before
      // a PHI node.
      auto *buf_ptr = builder.CreateConstInBoundsGEP2_32(
          arr_ty, buf, 0, 0, "");

      // Replace every use of the original global in this function.
      for (auto &site : sites) {
        if (site.via_ce) {
          site.inst->replaceUsesOfWith(site.via_ce, buf_ptr);
        } else {
          site.string_use->set(buf_ptr);
        }
      }
    }

    // Clean up dead ConstantExpr users (CE → GV ref may linger after
    // all instruction-level uses were rewritten above).
    info.gv->removeDeadConstantUsers();

    // If original global has no more uses, remove it.
    if (info.gv->use_empty()) {
      info.gv->eraseFromParent();
    }
  }
}

}  // namespace ollvm
