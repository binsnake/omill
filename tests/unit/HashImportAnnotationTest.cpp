#include "omill/Passes/HashImportAnnotation.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Passes/PassBuilder.h>

#include "omill/Utils/ImportHashDB.h"

#include <gtest/gtest.h>

namespace {

class HashImportAnnotationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    return M;
  }

  void runPass(llvm::Module &M) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

    llvm::ModulePassManager MPM;
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::HashImportAnnotationPass());
    MPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(FPM)));
    MPM.run(M, MAM);
  }
};

TEST_F(HashImportAnnotationTest, DetectsHashComparison) {
  auto M = createModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

  auto *fn_ty = llvm::FunctionType::get(void_ty, {i32_ty}, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  // Build a simple loop: entry -> loop_header -> [loop_body | exit]
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  auto *loop_hdr = llvm::BasicBlock::Create(Ctx, "loop", fn);
  auto *loop_body = llvm::BasicBlock::Create(Ctx, "body", fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", fn);

  // entry: br loop
  llvm::IRBuilder<> B(entry);
  B.CreateBr(loop_hdr);

  // loop: phi, icmp eq with hash constant, br cond exit, body
  B.SetInsertPoint(loop_hdr);
  auto *phi = B.CreatePHI(i32_ty, 2, "hash");
  phi->addIncoming(fn->getArg(0), entry);

  uint32_t target_hash =
      omill::ImportHashDB::computeHash("VirtualAlloc", 0x811c9dc5u);
  auto *icmp = B.CreateICmpEQ(phi,
                               llvm::ConstantInt::get(i32_ty, target_hash));
  B.CreateCondBr(icmp, exit_bb, loop_body);

  // body: update phi, br loop (back-edge)
  B.SetInsertPoint(loop_body);
  auto *next = B.CreateAdd(phi, llvm::ConstantInt::get(i32_ty, 1));
  phi->addIncoming(next, loop_body);
  B.CreateBr(loop_hdr);

  // exit: ret
  B.SetInsertPoint(exit_bb);
  B.CreateRetVoid();

  runPass(*M);

  // Find the icmp and check for metadata.
  bool found_metadata = false;
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        if (auto *md = cmp->getMetadata("omill.resolved_import")) {
          found_metadata = true;
          ASSERT_EQ(md->getNumOperands(), 2u);
          auto *mod_str =
              llvm::dyn_cast<llvm::MDString>(md->getOperand(0));
          auto *fn_str =
              llvm::dyn_cast<llvm::MDString>(md->getOperand(1));
          ASSERT_NE(mod_str, nullptr);
          ASSERT_NE(fn_str, nullptr);
          EXPECT_EQ(mod_str->getString(), "kernel32.dll");
          EXPECT_EQ(fn_str->getString(), "VirtualAlloc");
        }
      }
    }
  }
  EXPECT_TRUE(found_metadata);
}

TEST_F(HashImportAnnotationTest, NoFalsePositiveOnArbitraryConstant) {
  auto M = createModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

  auto *fn_ty = llvm::FunctionType::get(void_ty, {i32_ty}, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  // Build a loop with a non-hash constant in the icmp.
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  auto *loop_hdr = llvm::BasicBlock::Create(Ctx, "loop", fn);
  auto *loop_body = llvm::BasicBlock::Create(Ctx, "body", fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", fn);

  llvm::IRBuilder<> B(entry);
  B.CreateBr(loop_hdr);

  B.SetInsertPoint(loop_hdr);
  auto *phi = B.CreatePHI(i32_ty, 2, "val");
  phi->addIncoming(fn->getArg(0), entry);
  auto *icmp = B.CreateICmpEQ(phi,
                               llvm::ConstantInt::get(i32_ty, 0xABCDu));
  B.CreateCondBr(icmp, exit_bb, loop_body);

  B.SetInsertPoint(loop_body);
  auto *next = B.CreateAdd(phi, llvm::ConstantInt::get(i32_ty, 1));
  phi->addIncoming(next, loop_body);
  B.CreateBr(loop_hdr);

  B.SetInsertPoint(exit_bb);
  B.CreateRetVoid();

  runPass(*M);

  // No metadata should be added.
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        EXPECT_EQ(cmp->getMetadata("omill.resolved_import"), nullptr);
      }
    }
  }
}

TEST_F(HashImportAnnotationTest, MultipleHashComparisons) {
  auto M = createModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

  auto *fn_ty = llvm::FunctionType::get(void_ty, {i32_ty}, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  auto *loop_hdr = llvm::BasicBlock::Create(Ctx, "loop", fn);
  auto *check2_bb = llvm::BasicBlock::Create(Ctx, "check2", fn);
  auto *loop_body = llvm::BasicBlock::Create(Ctx, "body", fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", fn);

  llvm::IRBuilder<> B(entry);
  B.CreateBr(loop_hdr);

  // loop: phi, check hash 1 (VirtualAlloc)
  B.SetInsertPoint(loop_hdr);
  auto *phi = B.CreatePHI(i32_ty, 2, "hash");
  phi->addIncoming(fn->getArg(0), entry);

  uint32_t hash1 =
      omill::ImportHashDB::computeHash("VirtualAlloc", 0x811c9dc5u);
  auto *icmp1 = B.CreateICmpEQ(phi, llvm::ConstantInt::get(i32_ty, hash1));
  B.CreateCondBr(icmp1, exit_bb, check2_bb);

  // check2: check hash 2 (VirtualFree)
  B.SetInsertPoint(check2_bb);
  uint32_t hash2 =
      omill::ImportHashDB::computeHash("VirtualFree", 0x811c9dc5u);
  auto *icmp2 = B.CreateICmpEQ(phi, llvm::ConstantInt::get(i32_ty, hash2));
  B.CreateCondBr(icmp2, exit_bb, loop_body);

  // body: update phi, br loop
  B.SetInsertPoint(loop_body);
  auto *next = B.CreateAdd(phi, llvm::ConstantInt::get(i32_ty, 1));
  phi->addIncoming(next, loop_body);
  B.CreateBr(loop_hdr);

  // exit: ret
  B.SetInsertPoint(exit_bb);
  B.CreateRetVoid();

  runPass(*M);

  // Both icmp instructions should have metadata.
  unsigned metadata_count = 0;
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        if (cmp->getMetadata("omill.resolved_import"))
          metadata_count++;
      }
    }
  }
  EXPECT_EQ(metadata_count, 2u);
}

TEST_F(HashImportAnnotationTest, PairedCWImportHashResolution) {
  // Simulates CW_IMPORT pattern: two separate FNV loops in one function.
  // Loop 1: module hash (case-insensitive FNV1a32 of "kernel32.dll")
  // Loop 2: function hash (case-sensitive FNV1a32 of "VirtualAlloc")
  //
  // Strategy 2 may resolve the function hash alone — Strategy 3 should
  // still annotate the module hash by pairing it with the resolved function.
  auto M = createModule();
  auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
  auto *void_ty = llvm::Type::getVoidTy(Ctx);

  auto *fn_ty = llvm::FunctionType::get(void_ty, {i32_ty, i32_ty}, false);
  auto *fn = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "cw_import_fn", *M);

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", fn);
  // Loop 1: module hash
  auto *loop1_hdr = llvm::BasicBlock::Create(Ctx, "mod_loop", fn);
  auto *loop1_body = llvm::BasicBlock::Create(Ctx, "mod_body", fn);
  // Loop 2: function hash
  auto *loop2_hdr = llvm::BasicBlock::Create(Ctx, "fn_loop", fn);
  auto *loop2_body = llvm::BasicBlock::Create(Ctx, "fn_body", fn);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", fn);

  llvm::IRBuilder<> B(entry);
  B.CreateBr(loop1_hdr);

  // Module loop with FNV multiply and module hash comparison.
  B.SetInsertPoint(loop1_hdr);
  auto *phi1 = B.CreatePHI(i32_ty, 2, "mod_hash");
  phi1->addIncoming(fn->getArg(0), entry);

  // FNV-1a multiply (makes this loop recognizable as FNV).
  auto *fnv_mul1 =
      B.CreateMul(phi1, llvm::ConstantInt::get(i32_ty, 0x01000193u));

  uint32_t mod_hash = omill::ImportHashDB::computeHash(
      "kernel32.dll", omill::HashAlgorithm::FNV1a32_Lowercase, 0x811c9dc5u);
  auto *mod_icmp =
      B.CreateICmpEQ(fnv_mul1, llvm::ConstantInt::get(i32_ty, mod_hash));
  B.CreateCondBr(mod_icmp, loop2_hdr, loop1_body);

  B.SetInsertPoint(loop1_body);
  auto *next1 = B.CreateXor(phi1, llvm::ConstantInt::get(i32_ty, 0x42));
  phi1->addIncoming(next1, loop1_body);
  B.CreateBr(loop1_hdr);

  // Function loop with FNV multiply and function hash comparison.
  B.SetInsertPoint(loop2_hdr);
  auto *phi2 = B.CreatePHI(i32_ty, 2, "fn_hash");
  phi2->addIncoming(fn->getArg(1), loop1_hdr);

  auto *fnv_mul2 =
      B.CreateMul(phi2, llvm::ConstantInt::get(i32_ty, 0x01000193u));

  uint32_t func_hash = omill::ImportHashDB::computeHash(
      "VirtualAlloc", omill::HashAlgorithm::FNV1a32, 0x811c9dc5u);
  auto *fn_icmp =
      B.CreateICmpEQ(fnv_mul2, llvm::ConstantInt::get(i32_ty, func_hash));
  B.CreateCondBr(fn_icmp, exit_bb, loop2_body);

  B.SetInsertPoint(loop2_body);
  auto *next2 = B.CreateXor(phi2, llvm::ConstantInt::get(i32_ty, 0x42));
  phi2->addIncoming(next2, loop2_body);
  B.CreateBr(loop2_hdr);

  B.SetInsertPoint(exit_bb);
  B.CreateRetVoid();

  runPass(*M);

  // At least one icmp should be annotated with VirtualAlloc (function hash
  // resolves via Strategy 2). The module hash should also be annotated via
  // Strategy 3 pairing. Count total annotations.
  unsigned metadata_count = 0;
  bool has_func_annotation = false;
  bool has_module_annotation = false;
  for (auto &BB : *fn) {
    for (auto &I : BB) {
      if (auto *cmp = llvm::dyn_cast<llvm::ICmpInst>(&I)) {
        if (auto *md = cmp->getMetadata("omill.resolved_import")) {
          metadata_count++;
          auto *mod_str =
              llvm::dyn_cast<llvm::MDString>(md->getOperand(0));
          auto *fn_str =
              llvm::dyn_cast<llvm::MDString>(md->getOperand(1));
          if (mod_str && mod_str->getString() == "kernel32.dll") {
            if (fn_str && fn_str->getString() == "VirtualAlloc")
              has_func_annotation = true;
            else
              has_module_annotation = true;
          }
        }
      }
    }
  }
  // Function hash resolved (Strategy 2 or 3).
  EXPECT_TRUE(has_func_annotation);
  // Module hash annotated via Strategy 3 pairing.
  EXPECT_TRUE(has_module_annotation);
  EXPECT_EQ(metadata_count, 2u);
}

}  // namespace
