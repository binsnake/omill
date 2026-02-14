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

}  // namespace
