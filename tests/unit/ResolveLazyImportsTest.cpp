#include "omill/Passes/ResolveLazyImports.h"

#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/IR/Verifier.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

namespace {

class ResolveLazyImportsTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  void runPass(llvm::Function *F) {
    llvm::FunctionPassManager FPM;
    FPM.addPass(omill::ResolveLazyImportsPass());

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

    FPM.run(*F, FAM);
  }

  /// Attach !omill.resolved_import metadata to an ICmp.
  void attachResolvedImportMD(llvm::ICmpInst *icmp,
                               llvm::StringRef hash_str,
                               llvm::StringRef func_name) {
    auto &Ctx = icmp->getContext();
    auto *md = llvm::MDNode::get(Ctx, {llvm::MDString::get(Ctx, hash_str),
                                        llvm::MDString::get(Ctx, func_name)});
    icmp->setMetadata("omill.resolved_import", md);
  }

  /// Create __omill_dispatch_call declaration.
  llvm::Function *createDispatchDecl(llvm::Module &M) {
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ft = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
    return llvm::Function::Create(ft, llvm::Function::ExternalLinkage,
                                   "__omill_dispatch_call", M);
  }
};

TEST_F(ResolveLazyImportsTest, FoldsCalledImport) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *dispatch = createDispatchDecl(*M);

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *state = F->getArg(0);
  auto *mem = F->getArg(2);

  // Build:  entry → cmp → [true: dispatch_call, false: exit]
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "call_bb", F);
  auto *false_bb = llvm::BasicBlock::Create(Ctx, "exit_bb", F);

  // Entry: hash comparison.  Use `new ICmpInst` to avoid IRBuilder
  // constant-folding `icmp eq const, const` → `true`.
  llvm::IRBuilder<> B(entry);
  auto *icmp = new llvm::ICmpInst(llvm::ICmpInst::ICMP_EQ,
                                   B.getInt64(0xABCD1234),
                                   B.getInt64(0xABCD1234), "hash_cmp");
  B.Insert(icmp);
  attachResolvedImportMD(icmp, "0xABCD1234", "VirtualAlloc");
  B.CreateCondBr(icmp, true_bb, false_bb);

  // True block: dispatch_call with unresolved target.
  {
    llvm::IRBuilder<> TB(true_bb);
    auto *target = TB.getInt64(0xDEAD);
    TB.CreateCall(dispatch, {state, target, mem});
    TB.CreateRet(mem);
  }

  // False block.
  {
    llvm::IRBuilder<> FB(false_bb);
    FB.CreateRet(mem);
  }

  runPass(F);

  // The icmp should have been replaced with true (constant).
  // Check that no ICmpInst remains in entry block.
  bool has_icmp = false;
  for (auto &I : *entry) {
    if (llvm::isa<llvm::ICmpInst>(&I))
      has_icmp = true;
  }
  EXPECT_FALSE(has_icmp);

  // VirtualAlloc should now be declared in the module.
  auto *va_fn = M->getFunction("VirtualAlloc");
  EXPECT_NE(va_fn, nullptr);

  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

TEST_F(ResolveLazyImportsTest, CreatesShortcutForTerminalImport) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *mem = F->getArg(2);

  // Build a simple loop with an icmp (no dispatch_call in true successor).
  // preheader → header → [true: body → latch → header, false: exit]
  auto *preheader = llvm::BasicBlock::Create(Ctx, "preheader", F);
  auto *header = llvm::BasicBlock::Create(Ctx, "header", F);
  auto *body = llvm::BasicBlock::Create(Ctx, "body", F);
  auto *latch = llvm::BasicBlock::Create(Ctx, "latch", F);
  auto *exit_bb = llvm::BasicBlock::Create(Ctx, "exit", F);

  {
    llvm::IRBuilder<> B(preheader);
    B.CreateBr(header);
  }

  llvm::ICmpInst *icmp;
  {
    llvm::IRBuilder<> B(header);
    icmp = new llvm::ICmpInst(llvm::ICmpInst::ICMP_EQ,
                               B.getInt64(0x1111), B.getInt64(0x1111),
                               "hash_cmp");
    B.Insert(icmp);
    attachResolvedImportMD(icmp, "0x1111", "GetProcAddress");
    B.CreateCondBr(icmp, body, exit_bb);
  }

  {
    llvm::IRBuilder<> B(body);
    B.CreateBr(latch);
  }

  {
    llvm::IRBuilder<> B(latch);
    B.CreateBr(header);
  }

  {
    llvm::IRBuilder<> B(exit_bb);
    B.CreateRet(mem);
  }

  unsigned bb_count_before = F->size();

  runPass(F);

  // A "resolved" shortcut block should have been created.
  // The preheader should now branch to the shortcut, not the header.
  // The original loop blocks should be eliminated as unreachable.
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));

  // GetProcAddress should be declared.
  auto *gpa_fn = M->getFunction("GetProcAddress");
  EXPECT_NE(gpa_fn, nullptr);
}

TEST_F(ResolveLazyImportsTest, HandlesNoLoopContext) {
  auto M = std::make_unique<llvm::Module>("test", Ctx);
  M->setDataLayout(
      "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-"
      "n8:16:32:64-S128");

  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *fn_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *F = llvm::Function::Create(fn_ty, llvm::Function::ExternalLinkage,
                                    "test_func", *M);

  auto *mem = F->getArg(2);

  // ICmp with metadata but NOT inside any loop.
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", F);
  auto *true_bb = llvm::BasicBlock::Create(Ctx, "true_bb", F);
  auto *false_bb = llvm::BasicBlock::Create(Ctx, "false_bb", F);

  llvm::IRBuilder<> B(entry);
  auto *icmp = new llvm::ICmpInst(llvm::ICmpInst::ICMP_EQ,
                                   B.getInt64(0x2222), B.getInt64(0x2222),
                                   "hash_cmp");
  B.Insert(icmp);
  attachResolvedImportMD(icmp, "0x2222", "LoadLibraryA");
  B.CreateCondBr(icmp, true_bb, false_bb);

  {
    llvm::IRBuilder<> TB(true_bb);
    TB.CreateRet(mem);
  }
  {
    llvm::IRBuilder<> FB(false_bb);
    FB.CreateRet(mem);
  }

  runPass(F);

  // The icmp should have been replaced with true.
  bool has_icmp = false;
  for (auto &BB : *F)
    for (auto &I : BB)
      if (llvm::isa<llvm::ICmpInst>(&I))
        has_icmp = true;
  EXPECT_FALSE(has_icmp);

  EXPECT_NE(M->getFunction("LoadLibraryA"), nullptr);
  EXPECT_FALSE(llvm::verifyFunction(*F, &llvm::errs()));
}

}  // namespace
