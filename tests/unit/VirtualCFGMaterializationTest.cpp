#include "omill/Passes/VirtualCFGMaterialization.h"

#include <llvm/IR/CFG.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/Passes/PassBuilder.h>

#include <gtest/gtest.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Omill.h"

namespace {

class VirtualCFGMaterializationTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  std::unique_ptr<llvm::Module> createModule() {
    auto M = std::make_unique<llvm::Module>("virtual-cfg", Ctx);
    M->setDataLayout(
        "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-"
        "f80:128-n8:16:32:64-S128");
    return M;
  }

  void runPass(llvm::Module &M,
               std::optional<omill::BinaryMemoryMap> memory_map = std::nullopt) {
    llvm::PassBuilder PB;
    llvm::LoopAnalysisManager LAM;
    llvm::FunctionAnalysisManager FAM;
    llvm::CGSCCAnalysisManager CGAM;
    llvm::ModuleAnalysisManager MAM;

    if (memory_map.has_value()) {
      MAM.registerPass(
          [map = std::move(*memory_map)]() mutable {
            return omill::BinaryMemoryAnalysis(std::move(map));
          });
    }
    PB.registerModuleAnalyses(MAM);
    PB.registerCGSCCAnalyses(CGAM);
    PB.registerFunctionAnalyses(FAM);
    PB.registerLoopAnalyses(LAM);
    PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);
    omill::registerModuleAnalyses(MAM);

    llvm::ModulePassManager MPM;
    MPM.addPass(omill::VirtualCFGMaterializationPass());
    MPM.run(M, MAM);
  }

  void addMinimalX86FlagStateTypes(llvm::Module &M) {
    auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *aflags_ty = llvm::StructType::create(Ctx, "struct.ArithFlags");
    aflags_ty->setBody({i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty,
                        i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty, i8_ty},
                       false);

    auto *pad_ty = llvm::ArrayType::get(i8_ty, 0x810);
    auto *gpr_ty = llvm::StructType::create(Ctx, "struct.GPR");
    gpr_ty->setBody({i64_ty, i64_ty}, false);
    auto *x86_ty = llvm::StructType::create(Ctx, "struct.X86State");
    x86_ty->setBody({pad_ty, aflags_ty, gpr_ty}, false);

    auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
    state_ty->setBody({x86_ty}, false);
  }
};

TEST_F(VirtualCFGMaterializationTest, MaterializesDirectCallFromVirtualFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004600", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004500", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  auto *slot = B.CreateGEP(i8_ty, caller->getArg(0), B.getInt64(0x190));
  B.CreateStore(B.getInt64(0x180004600ULL), slot);
  auto *loaded = B.CreateLoad(i64_ty, slot);
  auto *call = B.CreateCall(dispatch, {caller->getArg(0), loaded, caller->getArg(2)});
  B.CreateRet(call);

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest, MaterializesMustTailJumpFromVirtualFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004800", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004700", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  auto *slot = B.CreateGEP(i8_ty, caller->getArg(0), B.getInt64(0x108));
  B.CreateStore(B.getInt64(0x180004800ULL), slot);
  auto *loaded = B.CreateLoad(i64_ty, slot);
  B.CreateCall(dispatch, {caller->getArg(0), loaded, caller->getArg(2)});
  B.CreateRet(caller->getArg(0));

  runPass(*M);

  unsigned dispatch_calls = 0;
  llvm::CallInst *direct_tail = nullptr;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        direct_tail = CI;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  ASSERT_NE(direct_tail, nullptr);
  EXPECT_EQ(direct_tail->getTailCallKind(), llvm::CallInst::TCK_MustTail);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesSelfMustTailJumpFromVirtualFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004900", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  auto *slot = B.CreateGEP(i8_ty, caller->getArg(0), B.getInt64(0x108));
  B.CreateStore(B.getInt64(0x180004900ULL), slot);
  auto *loaded = B.CreateLoad(i64_ty, slot);
  auto *dispatch_call =
      B.CreateCall(dispatch, {caller->getArg(0), loaded, caller->getArg(2)});
  B.CreateRet(dispatch_call);

  runPass(*M);

  unsigned dispatch_calls = 0;
  llvm::CallInst *self_tail = nullptr;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == caller)
        self_tail = CI;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  ASSERT_NE(self_tail, nullptr);
  EXPECT_EQ(self_tail->getTailCallKind(), llvm::CallInst::TCK_MustTail);
}

TEST_F(VirtualCFGMaterializationTest,
       CollapsesTerminalMissingBlockStubToDirectMissingBlockCall) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *state_ty = llvm::StructType::create(Ctx, "struct.State");
  state_ty->setBody({llvm::ArrayType::get(i8_ty, 4096)});

  auto *remill_bb = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", remill_bb);
    llvm::IRBuilder<> B(entry);
    B.CreateConstGEP1_64(i8_ty, remill_bb->getArg(0), 2472, "PC");
    B.CreateRet(remill_bb->getArg(2));
  }

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *missing = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_missing_block", *M);

  auto *stub = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_ffffffffac9b1737", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", stub);
    llvm::IRBuilder<> B(entry);
    auto *pc_gep = B.CreateConstGEP1_64(i8_ty, stub->getArg(0), 2472);
    B.CreateStore(stub->getArg(1), pc_gep);
    auto *result =
        B.CreateCall(missing, {stub->getArg(0), stub->getArg(1), stub->getArg(2)});
    B.CreateRet(result);
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_1800047f0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch, {caller->getArg(0),
                                         B.getInt64(0xFFFFFFFFAC9B1737ULL),
                                         caller->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  EXPECT_EQ(M->getFunction("blk_ffffffffac9b1737"), nullptr);
  EXPECT_FALSE(caller->isDeclaration());
  EXPECT_TRUE(dispatch->use_empty());

  bool saw_pc_store = false;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!SI)
        continue;
      auto *stored_pc = llvm::dyn_cast<llvm::ConstantInt>(SI->getValueOperand());
      if (!stored_pc)
        continue;
      if (stored_pc->getZExtValue() == 0xFFFFFFFFAC9B1737ULL)
        saw_pc_store = true;
    }
  }
  EXPECT_TRUE(saw_pc_store);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesTerminalMissingBlockFromNextPcFacts) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *jmpi = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_13JMPI2RnImLb1EEEEP6MemoryS4_R5StateT_3RnWImE", *M);
  auto *missing = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_missing_block", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180011140", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_1800110ce", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    B.CreateStore(B.getInt64(0x180011140ULL), next_pc);
    auto *target_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(jmpi, {caller->getArg(2), caller->getArg(0), target_pc, next_pc});
    auto *call = B.CreateCall(
        missing, {caller->getArg(0), B.getInt64(0xFFFFFFFFAC9B1737ULL),
                  caller->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned missing_calls = 0;
  unsigned direct_calls = 0;
  llvm::CallInst *direct_call = nullptr;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__remill_missing_block")
        ++missing_calls;
      if (callee == target) {
        ++direct_calls;
        direct_call = CI;
      }
    }
  }

  EXPECT_EQ(missing_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
  ASSERT_NE(direct_call, nullptr);
  auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(direct_call->getArgOperand(1));
  ASSERT_NE(pc_arg, nullptr);
  EXPECT_EQ(pc_arg->getZExtValue(), 0x180011140ULL);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesTerminalMissingBlockFromNearbyNextPcFacts) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *jmpi = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_13JMPI2RnImLb1EEEEP6MemoryS4_R5StateT_3RnWImE", *M);
  auto *missing = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_missing_block", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180021140", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_1800210ce", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    B.CreateStore(B.getInt64(0x180021145ULL), next_pc);
    auto *target_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(jmpi, {caller->getArg(2), caller->getArg(0), target_pc, next_pc});
    auto *call = B.CreateCall(
        missing, {caller->getArg(0), B.getInt64(0xFFFFFFFFAC9B1737ULL),
                  caller->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x4000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180020000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180020000ULL, image.data(), image.size(), false,
                /*executable=*/true);

  runPass(*M, std::move(map));

  unsigned missing_calls = 0;
  unsigned direct_calls = 0;
  llvm::CallInst *direct_call = nullptr;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__remill_missing_block")
        ++missing_calls;
      if (callee == target) {
        ++direct_calls;
        direct_call = CI;
      }
    }
  }

  EXPECT_EQ(missing_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
  ASSERT_NE(direct_call, nullptr);
  auto *pc_arg = llvm::dyn_cast<llvm::ConstantInt>(direct_call->getArgOperand(1));
  ASSERT_NE(pc_arg, nullptr);
  EXPECT_EQ(pc_arg->getZExtValue(), 0x180021140ULL);
}

TEST_F(VirtualCFGMaterializationTest,
       RewritesConstantMissingBlockCallToLiftedTarget) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *missing = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_missing_block", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000e240", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_18000e200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(missing, {caller->getArg(0),
                                        B.getInt64(0x18000E240ULL),
                                        caller->getArg(2)});
    call->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_disposition",
        "vm_exit_native_exec_unknown_return"));
    call->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_native_target_pc", "180020200"));
    call->addFnAttr(
        llvm::Attribute::get(Ctx, "omill.virtual_exit_partial", "1"));
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned missing_calls = 0;
  unsigned direct_calls = 0;
  llvm::CallInst *direct_call = nullptr;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__remill_missing_block")
        ++missing_calls;
      if (callee == target) {
        ++direct_calls;
        direct_call = CI;
      }
    }
  }

  EXPECT_EQ(missing_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
  ASSERT_NE(direct_call, nullptr);
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_exec_unknown_return");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_native_target_pc"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_native_target_pc")
                .getValueAsString(),
            "180020200");
  EXPECT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_partial"));
}

TEST_F(VirtualCFGMaterializationTest, LeavesDynamicDispatchUnchanged) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180004900", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  auto *dynamic_target = B.CreateAdd(caller->getArg(1), B.getInt64(0x20));
  B.CreateCall(dispatch, {caller->getArg(0), dynamic_target, caller->getArg(2)});
  B.CreateRet(caller->getArg(0));

  runPass(*M);

  unsigned dispatch_calls = 0;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest, MaterializesKnownProtectedBoundaryCall) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180004700", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  auto *call = B.CreateCall(dispatch,
                            {caller->getArg(0), B.getInt64(0x1800042BA4ULL),
                             caller->getArg(2)});
  B.CreateRet(call);

  omill::BinaryMemoryMap mem;
  uint8_t region[0x40] = {};
  region[0x00] = 0x68;
  region[0x05] = 0xE9;
  region[0x06] = 0x14;
  region[0x1E] = 0xE9;
  region[0x1F] = 0x0B;
  region[0x30] = 0xC3;
  mem.addRegion(0x1800042BA4ULL, region, sizeof(region), /*read_only=*/true);

  runPass(*M, std::move(mem));

  unsigned dispatch_calls = 0;
  llvm::Function *boundary = nullptr;
  llvm::CallInst *boundary_call = nullptr;
  for (auto &BB : *caller) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee->getName() == "vm_entry_1800042ba4") {
        boundary = callee;
        boundary_call = CI;
      }
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  ASSERT_NE(boundary, nullptr);
  ASSERT_NE(boundary_call, nullptr);
  EXPECT_TRUE(boundary->hasFnAttribute("omill.protection_boundary"));
  EXPECT_EQ(boundary->getFnAttribute("omill.boundary_kind").getValueAsString(),
            "vm_entry_stub");
  ASSERT_TRUE(boundary_call->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(boundary_call->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_terminal");
}

TEST_F(VirtualCFGMaterializationTest, MaterializesSelectDispatchFromCompareFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target_true = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005600", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_true);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_true->getArg(0));
  }

  auto *target_false = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005700", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_false);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_false->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180005500", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  llvm::IRBuilder<> B(entry);
  auto *slot_flag = B.CreateGEP(i8_ty, caller->getArg(0), B.getInt64(0x190));
  B.CreateStore(B.getInt64(1), slot_flag);
  auto *loaded_flag = B.CreateLoad(i64_ty, slot_flag);
  auto *cmp = B.CreateICmpEQ(loaded_flag, B.getInt64(1));
  auto *target_pc = B.CreateSelect(cmp, B.getInt64(0x180005600ULL),
                                   B.getInt64(0x180005700ULL));
  auto *call =
      B.CreateCall(dispatch, {caller->getArg(0), target_pc, caller->getArg(2)});
  B.CreateRet(call);

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned true_calls = 0;
  unsigned false_calls = 0;
  unsigned cond_branches = 0;
  for (auto &BB : *caller) {
    if (auto *branch = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
        branch && branch->isConditional()) {
      ++cond_branches;
    }
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target_true)
        ++true_calls;
      if (callee == target_false)
        ++false_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(true_calls, 1u);
  EXPECT_EQ(false_calls, 1u);
  EXPECT_EQ(cond_branches, 1u);
}

TEST_F(VirtualCFGMaterializationTest, MaterializesPhiDispatchAsSwitch) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005900", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005a00", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *caller = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180005800", *M);
  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
  auto *lhs = llvm::BasicBlock::Create(Ctx, "lhs", caller);
  auto *rhs = llvm::BasicBlock::Create(Ctx, "rhs", caller);
  auto *join = llvm::BasicBlock::Create(Ctx, "join", caller);

  {
    llvm::IRBuilder<> B(entry);
    B.CreateCondBr(B.getTrue(), lhs, rhs);
  }
  {
    llvm::IRBuilder<> B(lhs);
    B.CreateBr(join);
  }
  {
    llvm::IRBuilder<> B(rhs);
    B.CreateBr(join);
  }
  {
    llvm::IRBuilder<> B(join);
    auto *phi = B.CreatePHI(i64_ty, 2);
    phi->addIncoming(B.getInt64(0x180005900ULL), lhs);
    phi->addIncoming(B.getInt64(0x180005A00ULL), rhs);
    auto *call = B.CreateCall(dispatch, {caller->getArg(0), phi, caller->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  unsigned switch_terms = 0;
  for (auto &BB : *caller) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_terms;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target_a || callee == target_b)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 2u);
  EXPECT_EQ(switch_terms, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromIncomingPhiFactsAsSwitch) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005b00", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005c00", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180005a00", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x190));
    auto *target = B.CreateLoad(i64_ty, slot);
    auto *call =
        B.CreateCall(dispatch, {helper->getArg(0), target, helper->getArg(2)});
    B.CreateRet(call);
  }

  auto build_caller = [&](llvm::StringRef name, uint64_t pc) {
    auto *caller = llvm::Function::Create(lifted_ty,
                                          llvm::Function::ExternalLinkage,
                                          name, *M);
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, caller->getArg(0), B.getInt64(0x190));
    B.CreateStore(B.getInt64(pc), slot);
    auto *call =
        B.CreateCall(helper, {caller->getArg(0), caller->getArg(1), caller->getArg(2)});
    B.CreateRet(call);
  };
  build_caller("sub_180005800", 0x180005B00ULL);
  build_caller("sub_180005900", 0x180005C00ULL);

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  unsigned switch_terms = 0;
  for (auto &BB : *helper) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_terms;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target_a || callee == target_b)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 2u);
  EXPECT_EQ(switch_terms, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromBoundaryAdjacentRegionFacts) {
  auto M = createModule();
  auto *void_ty = llvm::Type::getVoidTy(Ctx);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);
  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180006300", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180006200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.getInt64(0x180006300ULL), slot_target);
    llvm::SmallVector<llvm::Value *, 12> boundary_args(12, B.getInt64(0));
    boundary_args[0] = vip;
    B.CreateCall(boundary_ty, boundary, boundary_args);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180006100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *slot_vip = B.CreateGEP(i8_ty, state, B.getInt64(0x108));
    auto *slot_target = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    llvm::SmallVector<llvm::Value *, 12> boundary_args(12, B.getInt64(0));
    boundary_args[0] = vip;
    B.CreateCall(boundary_ty, boundary, boundary_args);
    B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    auto *loaded_target = B.CreateLoad(i64_ty, slot_target);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_target, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromRegionFactsToBlockHandler) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *boundary_ty =
      llvm::FunctionType::get(i64_ty, std::vector<llvm::Type *>(12, i64_ty),
                              false);

  auto *boundary = llvm::Function::Create(boundary_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180006500", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180006420", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot_target = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x190));
    auto *slot_vip = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x108));
    auto *vip = B.CreateLoad(i64_ty, slot_vip);
    B.CreateStore(B.getInt64(0x180006500ULL), slot_target);
    llvm::SmallVector<llvm::Value *, 12> boundary_args(12, B.getInt64(0));
    boundary_args[0] = vip;
    B.CreateCall(boundary_ty, boundary, boundary_args);
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180006400", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_target = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x190));
    B.CreateCall(helper, {root->getArg(0), root->getArg(1), root->getArg(2)});
    auto *loaded_target = B.CreateLoad(i64_ty, slot_target);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_target, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       ContinuesProtectedBoundaryDispatchToLiftedCanonicalTarget) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *boundary = llvm::Function::Create(lifted_ty,
                                          llvm::Function::ExternalLinkage,
                                          "vm_entry_180042ba4", *M);
  boundary->addFnAttr("omill.protection_boundary");
  boundary->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary->addFnAttr("omill.boundary_entry_va", "180042BA4");
  boundary->addFnAttr("omill.boundary_target_va", "180055365");

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *continued = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180055365", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continued);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continued->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180042BA4ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned boundary_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == boundary || callee->getName() == "vm_entry_180042ba4")
        ++boundary_calls;
      if (callee == continued)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(boundary_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       SpecializesRootScopedHelperPerCallsiteFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180007100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180007200", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *helper = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_180007000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *slot_base = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x190));
    auto *slot_delta = B.CreateGEP(i8_ty, helper->getArg(0), B.getInt64(0x198));
    auto *base = B.CreateLoad(i64_ty, slot_base);
    auto *delta = B.CreateLoad(i64_ty, slot_delta);
    auto *target_pc = B.CreateAdd(base, delta);
    auto *call =
        B.CreateCall(dispatch, {helper->getArg(0), target_pc, helper->getArg(2)});
    B.CreateRet(call);
  }

  auto *caller_a = llvm::Function::Create(lifted_ty,
                                          llvm::Function::ExternalLinkage,
                                          "sub_180006f00", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_a);
    llvm::IRBuilder<> B(entry);
    auto *slot_base = B.CreateGEP(i8_ty, caller_a->getArg(0), B.getInt64(0x190));
    auto *slot_delta = B.CreateGEP(i8_ty, caller_a->getArg(0), B.getInt64(0x198));
    B.CreateStore(B.getInt64(0x1800070F0ULL), slot_base);
    B.CreateStore(B.getInt64(0x10), slot_delta);
    auto *call =
        B.CreateCall(helper, {caller_a->getArg(0), caller_a->getArg(1),
                              caller_a->getArg(2)});
    B.CreateRet(call);
  }

  auto *caller_b = llvm::Function::Create(lifted_ty,
                                          llvm::Function::ExternalLinkage,
                                          "sub_180006f40", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", caller_b);
    llvm::IRBuilder<> B(entry);
    auto *slot_base = B.CreateGEP(i8_ty, caller_b->getArg(0), B.getInt64(0x190));
    auto *slot_delta = B.CreateGEP(i8_ty, caller_b->getArg(0), B.getInt64(0x198));
    B.CreateStore(B.getInt64(0x1800071F0ULL), slot_base);
    B.CreateStore(B.getInt64(0x10), slot_delta);
    auto *call =
        B.CreateCall(helper, {caller_b->getArg(0), caller_b->getArg(1),
                              caller_b->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180001850", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    B.CreateCall(caller_a, {root->getArg(0), root->getArg(1), root->getArg(2)});
    auto *call =
        B.CreateCall(caller_b, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned base_helper_calls = 0;
  unsigned specialized_calls = 0;
  llvm::SmallVector<llvm::Function *, 4> specialized_helpers;
  for (auto &F : *M) {
    if (!F.hasFnAttribute("omill.virtual_specialized"))
      continue;
    specialized_helpers.push_back(&F);
  }

  for (llvm::Function *caller : {caller_a, caller_b}) {
    for (auto &BB : *caller) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee == helper)
          ++base_helper_calls;
        if (callee->hasFnAttribute("omill.virtual_specialized"))
          ++specialized_calls;
      }
    }
  }

  unsigned dispatch_calls = 0;
  unsigned direct_target_calls = 0;
  auto count_targets_in = [&](llvm::Function *F) {
    for (auto &BB : *F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_call")
          ++dispatch_calls;
        if (callee == target_a || callee == target_b)
          ++direct_target_calls;
      }
    }
  };

  count_targets_in(helper);
  for (auto *specialized : specialized_helpers) {
    EXPECT_TRUE(
        specialized->hasFnAttribute("omill.virtual_specialization.root_va"));
    count_targets_in(specialized);
  }

  if (specialized_helpers.size() == 0) {
    EXPECT_EQ(base_helper_calls, 2u);
    EXPECT_EQ(specialized_calls, 0u);
  } else {
    EXPECT_EQ(specialized_helpers.size(), 2u);
    EXPECT_EQ(base_helper_calls, 0u);
    EXPECT_EQ(specialized_calls, 2u);
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_target_calls, 2u);
}

TEST_F(VirtualCFGMaterializationTest, MarksClosedRootSliceFunctionsForCleanup) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180008100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180008000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x180008100ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  auto *scope_flag = M->getModuleFlag("omill.closed_root_slice_scope");
  ASSERT_NE(scope_flag, nullptr);
  auto *scope_ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(scope_flag);
  ASSERT_NE(scope_ci, nullptr);
  EXPECT_EQ(scope_ci->getZExtValue(), 1u);
  EXPECT_TRUE(root->hasFnAttribute("omill.closed_root_slice"));
  EXPECT_TRUE(root->hasFnAttribute("omill.closed_root_slice_root"));
  EXPECT_TRUE(target->hasFnAttribute("omill.closed_root_slice"));
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromHelperWrittenNextPcFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *helper_jump_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180008320", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *store_helper = llvm::Function::Create(
      helper_store_ty, llvm::Function::ExternalLinkage, "helper_store_slot", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(store_helper->getArg(3), store_helper->getArg(2));
    B.CreateRet(store_helper->getArg(0));
  }

  auto *jump_helper = llvm::Function::Create(
      helper_jump_ty, llvm::Function::ExternalLinkage, "helper_write_next_pc", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jump_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jump_helper->getArg(2), jump_helper->getArg(3));
    B.CreateRet(jump_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180008300", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *rdi = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x120));
    B.CreateCall(store_helper,
                 {root->getArg(2), root->getArg(0), rdi,
                  B.getInt64(0x180008320ULL)});
    auto *loaded_reg = B.CreateLoad(i64_ty, rdi);
    B.CreateCall(jump_helper,
                 {root->getArg(2), root->getArg(0), loaded_reg, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchAfterHelperByteWriteToOverlappingWideSlot) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i8_ty}, false);
  auto *helper_jump_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180008420", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *store_byte_helper = llvm::Function::Create(
      helper_store_ty, llvm::Function::ExternalLinkage,
      "helper_store_byte_slot", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_byte_helper);
    llvm::IRBuilder<> B(entry);
    auto *byte_slot =
        B.CreateGEP(i8_ty, store_byte_helper->getArg(1), B.getInt64(0x120));
    B.CreateStore(store_byte_helper->getArg(2), byte_slot);
    B.CreateRet(store_byte_helper->getArg(0));
  }

  auto *jump_helper = llvm::Function::Create(
      helper_jump_ty, llvm::Function::ExternalLinkage, "helper_write_next_pc",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jump_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jump_helper->getArg(2), jump_helper->getArg(3));
    B.CreateRet(jump_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180008400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *wide_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x120));
    B.CreateStore(B.getInt64(0x180008400ULL), wide_slot);
    (void) B.CreateLoad(i8_ty, wide_slot);
    B.CreateCall(store_byte_helper,
                 {root->getArg(2), root->getArg(0), B.getInt8(0x20)});
    auto *loaded_reg = B.CreateLoad(i64_ty, wide_slot);
    B.CreateCall(jump_helper,
                 {root->getArg(2), root->getArg(0), loaded_reg, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromHelperMaskedLowByteReconstruction) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180008520", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180008500", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *state = helper->getArg(0);
    auto *vip_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x120));
    auto *target_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    auto *vip = B.CreateLoad(i64_ty, vip_slot);
    auto *masked_high = B.CreateAnd(vip, B.getInt64(0xFFFFFFFFFFFFFF00ULL));
    auto *masked_low =
        B.CreateAnd(B.CreateZExt(B.CreateTrunc(vip, i8_ty), i64_ty),
                    B.getInt64(0xFF));
    B.CreateStore(B.CreateOr(masked_high, masked_low), target_slot);
    B.CreateRet(state);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_1800084f0", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *state = root->getArg(0);
    auto *vip_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x120));
    auto *target_slot = B.CreateGEP(i8_ty, state, B.getInt64(0x190));
    B.CreateStore(B.getInt64(0x180008520ULL), vip_slot);
    B.CreateCall(helper, {state, root->getArg(1), root->getArg(2)});
    auto *loaded_target = B.CreateLoad(i64_ty, target_slot);
    auto *call = B.CreateCall(dispatch,
                              {state, loaded_target, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromNestedMaskedPhiReconstruction) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target0 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_180061a0e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target0);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target0->getArg(0));
  }

  auto *target1 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18006a04d", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target1);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target1->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::GlobalValue::ExternalLinkage,
                                      "sub_18000f100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *then_bb = llvm::BasicBlock::Create(Ctx, "then", root);
    auto *else_bb = llvm::BasicBlock::Create(Ctx, "else", root);
    auto *merge_bb = llvm::BasicBlock::Create(Ctx, "merge", root);

    llvm::IRBuilder<> B(entry);
    auto *flag_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x811));
    auto *flag = B.CreateLoad(i8_ty, flag_slot);
    B.CreateCondBr(B.CreateICmpNE(flag, B.getInt8(0)), then_bb, else_bb);

    B.SetInsertPoint(then_bb);
    B.CreateBr(merge_bb);

    B.SetInsertPoint(else_bb);
    B.CreateBr(merge_bb);

    B.SetInsertPoint(merge_bb);
    auto *wide_phi = B.CreatePHI(i64_ty, 2);
    wide_phi->addIncoming(B.getInt64(0x18005C2F4ULL), then_bb);
    wide_phi->addIncoming(B.getInt64(0x180064933ULL), else_bb);
    auto *low8_phi = B.CreatePHI(i64_ty, 2);
    low8_phi->addIncoming(B.getInt64(0xF4), then_bb);
    low8_phi->addIncoming(B.getInt64(0x33), else_bb);
    auto *low16_phi = B.CreatePHI(i64_ty, 2);
    low16_phi->addIncoming(B.getInt64(0xC2F4), then_bb);
    low16_phi->addIncoming(B.getInt64(0x4933), else_bb);

    auto *inner = B.CreateOr(
        B.CreateAnd(wide_phi, B.getInt64(0xFFFFFFFFFFFFFF00ULL)),
        B.CreateAnd(low8_phi, B.getInt64(0xFF)));
    auto *outer = B.CreateOr(
        B.CreateAnd(inner, B.getInt64(0xFFFFFFFFFFFF0000ULL)),
        B.CreateAnd(low16_phi, B.getInt64(0xFFFF)));
    auto *target_pc = B.CreateAdd(outer, B.getInt64(0x571A));
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_target0_calls = 0;
  unsigned direct_target1_calls = 0;
  unsigned switch_count = 0;
  for (auto &BB : *root) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_count;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target0)
        ++direct_target0_calls;
      if (callee == target1)
        ++direct_target1_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_target0_calls, 1u);
  EXPECT_EQ(direct_target1_calls, 1u);
  EXPECT_EQ(switch_count, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromVmStackHelperFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180009520", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_push_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), sp, push_helper->getArg(1)});
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_pop_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, pop_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {pop_helper->getArg(2), sp});
    B.CreateStore(value, pop_helper->getArg(1));
    B.CreateRet(pop_helper->getArg(2));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009500", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *stack_cell = B.CreateAlloca(i64_ty, nullptr, "vm_stack");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_cell, i64_ty), sp_slot);
    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x180009520ULL), root->getArg(2)});
    B.CreateCall(pop_ty, pop_helper,
                 {root->getArg(0), next_pc, root->getArg(2)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromHelperRelativeVmStackFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180009620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_push_vm_stack", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), sp, push_helper->getArg(1)});
    B.CreateRet(next_memory);
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_pop_vm_stack_arg1_state", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {helper->getArg(0), sp});
    B.CreateStore(value, helper->getArg(2));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009600", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(i64_ty, nullptr, "vm_stack");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(vm_stack, i64_ty), sp_slot);
    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x180009620ULL), root->getArg(2)});
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromHelperReadMemoryThroughAddressArgument) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180009920", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_load_vm_stack_addr_arg", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *value = B.CreateCall(
        read_mem, {helper->getArg(0), helper->getArg(2)});
    B.CreateStore(value, helper->getArg(1));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009900", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(i64_ty, nullptr, "vm_stack");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(vm_stack, i64_ty), sp_slot);
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *addr = B.CreateAdd(sp, B.getInt64(0x10));
    B.CreateCall(write_mem,
                 {root->getArg(2), addr, B.getInt64(0x180009920ULL)});
    B.CreateCall(helper, {root->getArg(2), next_pc, addr});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromResolvedCallSiteReturnState) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000e140", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *call_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_18000e080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, call_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x18000E160ULL), rax_slot);
    B.CreateRet(call_target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000e013", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, continuation->getArg(0), B.getInt64(0x8A8));
    auto *value = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(value, B.getInt64(0x20));
    auto *call = B.CreateCall(
        dispatch, {continuation->getArg(0), target_pc, continuation->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000E080ULL), next_pc,
                         B.getInt64(0x18000E013ULL), return_pc});
    auto *cont = B.CreateCall(continuation,
                              {root->getArg(0), B.getInt64(0x18000E013ULL),
                               root->getArg(2)});
    B.CreateRet(cont);
  }

  std::vector<uint8_t> image(0x20000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false);

  runPass(*M, std::move(map));

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *continuation) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == final_target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromReturnPcSeededCallSiteTarget) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180011140", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *call_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180011080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, call_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x180011160ULL), rax_slot);
    B.CreateRet(call_target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180011013", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, continuation->getArg(0), B.getInt64(0x8A8));
    auto *value = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(value, B.getInt64(0x20));
    auto *call = B.CreateCall(
        dispatch, {continuation->getArg(0), target_pc, continuation->getArg(2)});
    B.CreateRet(call);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180011000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    auto *seeded_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *seeded_target = B.CreateAdd(seeded_return_pc, B.getInt64(0x6D));
    B.CreateStore(seeded_target, next_pc);
    auto *target_pc = B.CreateLoad(i64_ty, next_pc);
    auto *helper_return_pc = B.CreateLoad(i64_ty, return_pc);
    B.CreateCall(calli, {root->getArg(2), root->getArg(0), target_pc, next_pc,
                         helper_return_pc, return_pc});
    auto *call_result = B.CreateCall(
        call_target,
        {root->getArg(0), B.getInt64(0x180011080ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x180011013ULL), call_result});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x40000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(),
                /*read_only=*/false, /*executable=*/false);

  runPass(*M, std::move(map));

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *continuation) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == final_target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromPreludeDirectCallReturnFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *prelude_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", prelude_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, prelude_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x1800106DDULL), rax_slot);
    B.CreateRet(prelude_target->getArg(0));
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, mid->getArg(0), B.getInt64(0x8A8));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(rax, B.getInt64(0x5DDULL));
    auto *call = B.CreateCall(dispatch, {mid->getArg(0), target_pc, mid->getArg(2)});
    B.CreateRet(call);
  }

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  runPass(*M, std::move(map));

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *mid) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == final_target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesPreludeTargetDispatchFromPredecessorLocalizedFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *prelude_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", prelude_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, prelude_target->getArg(0), B.getInt64(0x8A8));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(rax, B.getInt64(0x5DDULL));
    auto *call = B.CreateCall(
        dispatch, {prelude_target->getArg(0), target_pc, prelude_target->getArg(2)});
    B.CreateRet(call);
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, mid->getArg(0), B.getInt64(0x8A8));
    (void) B.CreateLoad(i64_ty, rax_slot);
    B.CreateRet(mid->getArg(0));
  }

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x1800106DDULL), rax_slot);
    auto *call =
        B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x200, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  runPass(*M, std::move(map));

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *prelude_target) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == final_target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromPreludeNestedCallSiteReturnFacts) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *inner_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_1800100c0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", inner_target);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot =
        B.CreateGEP(i8_ty, inner_target->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.getInt64(0x1800106DDULL), rax_slot);
    B.CreateRet(inner_target->getArg(0));
  }

  auto *inner_cont = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010093", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", inner_cont);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(inner_cont->getArg(0));
  }

  auto *prelude_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", prelude_target);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {prelude_target->getArg(2), prelude_target->getArg(0),
                         B.getInt64(0x1800100C0ULL), next_pc,
                         B.getInt64(0x180010093ULL), return_pc});
    auto *call_result = B.CreateCall(
        inner_target,
        {prelude_target->getArg(0), B.getInt64(0x1800100C0ULL),
         prelude_target->getArg(2)});
    auto *tail = B.CreateCall(
        inner_cont,
        {prelude_target->getArg(0), B.getInt64(0x180010093ULL), call_result});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  auto *mid = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                     "blk_18001000e", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", mid);
    llvm::IRBuilder<> B(entry);
    auto *rax_slot = B.CreateGEP(i8_ty, mid->getArg(0), B.getInt64(0x8A8));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    auto *target_pc = B.CreateSub(rax, B.getInt64(0x5DDULL));
    auto *call = B.CreateCall(dispatch, {mid->getArg(0), target_pc, mid->getArg(2)});
    B.CreateRet(call);
  }

  auto *final_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", final_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(final_target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(mid, {root->getArg(0), root->getArg(1), root->getArg(2)});
    B.CreateRet(call);
  }

  std::vector<uint8_t> image(0x300, 0x90);
  image[0x09] = 0xE8;
  image[0x0A] = 0x72;
  image[0x0B] = 0x00;
  image[0x0C] = 0x00;
  image[0x0D] = 0x00;

  omill::BinaryMemoryMap map;
  map.setImageBase(0x180010000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180010000ULL, image.data(), image.size(), false);

  runPass(*M, std::move(map));

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *mid) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == final_target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromHelperVmStackReadsWithCallerSpDelta) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_1800096A0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage,
      "helper_push_vm_stack_with_sp_decrement_addr_arg_chain", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    B.CreateStore(new_sp, sp_slot);
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), new_sp, push_helper->getArg(1)});
    B.CreateRet(next_memory);
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_pop_vm_stack_arg1_state", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {helper->getArg(0), sp});
    B.CreateStore(value, helper->getArg(2));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180009680", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x1800096A0ULL), root->getArg(2)});
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromVmStackReturnPcLoadedFromCallerAlloca) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *call_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty}, false);
  auto *jump_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000AC20", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *call_helper = llvm::Function::Create(
      call_ty, llvm::Function::ExternalLinkage, "helper_push_return_pc", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, call_helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory = B.CreateCall(
        write_mem, {call_helper->getArg(0), new_sp, call_helper->getArg(2)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateStore(call_helper->getArg(2), call_helper->getArg(3));
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_pop_vm_stack_to_tmp",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, pop_helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *value = B.CreateCall(read_mem, {pop_helper->getArg(0), sp});
    B.CreateStore(B.CreateAdd(sp, B.getInt64(8)), sp_slot);
    B.CreateStore(value, pop_helper->getArg(2));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *jump_helper = llvm::Function::Create(
      jump_ty, llvm::Function::ExternalLinkage, "helper_write_next_pc", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jump_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jump_helper->getArg(2), jump_helper->getArg(3));
    B.CreateRet(jump_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000AC00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    auto *tmp = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    B.CreateStore(B.getInt64(0x18000AC00ULL), return_pc);
    auto *loaded_return_pc = B.CreateLoad(i64_ty, return_pc);
    B.CreateCall(call_ty, call_helper,
                 {root->getArg(2), root->getArg(0), loaded_return_pc,
                  return_pc});
    B.CreateCall(pop_ty, pop_helper, {root->getArg(2), root->getArg(0), tmp});
    auto *loaded_tmp = B.CreateLoad(i64_ty, tmp);
    auto *target_pc = B.CreateAdd(loaded_tmp, B.getInt64(0x20));
    B.CreateCall(jump_ty, jump_helper,
                 {root->getArg(2), root->getArg(0), target_pc, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromVmStackLoadAfterRepeatedPushes) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 4);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false);
  auto *store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);
  auto *load_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000AE20", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_push_vm_stack_qword",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot =
        B.CreateGEP(i8_ty, push_helper->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(2), new_sp,
                                 push_helper->getArg(1)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateRet(next_memory);
  }

  auto *store_helper = llvm::Function::Create(
      store_ty, llvm::Function::ExternalLinkage, "helper_store_vm_stack_addr",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    auto *next_memory =
        B.CreateCall(write_mem, {store_helper->getArg(0), store_helper->getArg(1),
                                 store_helper->getArg(2)});
    B.CreateRet(next_memory);
  }

  auto *load_helper = llvm::Function::Create(
      load_ty, llvm::Function::ExternalLinkage, "helper_load_vm_stack_addr",
      *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", load_helper);
    llvm::IRBuilder<> B(entry);
    auto *value =
        B.CreateCall(read_mem, {load_helper->getArg(0), load_helper->getArg(2)});
    B.CreateStore(value, load_helper->getArg(1));
    B.CreateRet(load_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000AE00", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *entry_sp = B.CreateGEP(stack_array_ty, vm_stack,
                                 {B.getInt64(0), B.getInt64(2)});
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    auto *rax_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(B.CreatePtrToInt(entry_sp, i64_ty), sp_slot);

    auto *sp0 = B.CreateLoad(i64_ty, sp_slot);
    B.CreateCall(store_ty, store_helper,
                 {root->getArg(2), sp0, B.getInt64(0x18000AE20ULL)});
    B.CreateStore(B.getInt64(0x1111222233334444ULL), rax_slot);

    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x10101010ULL), root->getArg(2)});
    auto *sp1 = B.CreateLoad(i64_ty, sp_slot);
    auto *addr1 = B.CreateAdd(sp1, B.getInt64(16));
    auto *rax = B.CreateLoad(i64_ty, rax_slot);
    B.CreateCall(store_ty, store_helper, {root->getArg(2), addr1, rax});

    B.CreateCall(push_ty, push_helper,
                 {root->getArg(0), B.getInt64(0x20202020ULL), root->getArg(2)});
    auto *sp2 = B.CreateLoad(i64_ty, sp_slot);
    auto *addr2 = B.CreateAdd(sp2, B.getInt64(16));
    B.CreateCall(load_ty, load_helper, {root->getArg(2), next_pc, addr2});

    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateCall(dispatch,
                 {root->getArg(0), loaded_next_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromLiftedCallContinuationReturnAddress) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *remill_bb = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", remill_bb);
    llvm::IRBuilder<> B(entry);
    B.CreateGEP(i8_ty, remill_bb->getArg(0), B.getInt64(0x908), "RSP");
    B.CreateRet(remill_bb->getArg(2));
  }

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180010320", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010300", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation->getArg(0));
  }

  auto *trampoline = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010280", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", trampoline);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, trampoline->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *ret_pc = B.CreateCall(read_mem, {trampoline->getArg(2), sp});
    auto *target_pc = B.CreateAdd(ret_pc, B.getInt64(0x20));
    B.CreateStore(target_pc, next_pc);
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *next_memory = B.CreateCall(
        dispatch, {trampoline->getArg(0), loaded_next_pc, trampoline->getArg(2)});
    B.CreateRet(next_memory);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180010260", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call_memory = B.CreateCall(
        lifted_ty, trampoline,
        {root->getArg(0), B.getInt64(0x180010280ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        lifted_ty, continuation,
        {root->getArg(0), B.getInt64(0x180010300ULL), call_memory});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  llvm::CallInst *direct_call = nullptr;
  for (auto &BB : *trampoline) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target) {
        ++direct_calls;
        direct_call = CI;
      }
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
  ASSERT_NE(direct_call, nullptr);
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "stay_in_vm");
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesLiftedCallContinuationDispatchPerCallsiteWithStackSpecialization) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *remill_bb = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__remill_basic_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", remill_bb);
    llvm::IRBuilder<> B(entry);
    B.CreateGEP(i8_ty, remill_bb->getArg(0), B.getInt64(0x908), "RSP");
    B.CreateRet(remill_bb->getArg(2));
  }

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010520", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010620", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *continuation_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010500", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation_a->getArg(0));
  }

  auto *continuation_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010600", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", continuation_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(continuation_b->getArg(0));
  }

  auto *trampoline = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010480", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", trampoline);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, trampoline->getArg(0), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *ret_pc = B.CreateCall(read_mem, {trampoline->getArg(2), sp});
    auto *target_pc = B.CreateAdd(ret_pc, B.getInt64(0x20));
    B.CreateStore(target_pc, next_pc);
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    auto *next_memory = B.CreateCall(
        dispatch, {trampoline->getArg(0), loaded_next_pc, trampoline->getArg(2)});
    B.CreateRet(next_memory);
  }

  auto make_root = [&](llvm::StringRef name, llvm::Function *continuation,
                       uint64_t continuation_pc) {
    auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        name, *M);
    root->addFnAttr("omill.output_root");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call_memory = B.CreateCall(
        lifted_ty, trampoline,
        {root->getArg(0), B.getInt64(0x180010480ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        lifted_ty, continuation,
        {root->getArg(0), B.getInt64(continuation_pc), call_memory});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
    return root;
  };

  auto *root_a = make_root("sub_180010460", continuation_a, 0x180010500ULL);
  auto *root_b = make_root("sub_180010560", continuation_b, 0x180010600ULL);

  runPass(*M);

  llvm::SmallPtrSet<llvm::Function *, 4> called_callees;
  unsigned base_trampoline_calls = 0;
  unsigned specialized_calls = 0;
  for (llvm::Function *root : {root_a, root_b}) {
    for (auto &BB : *root) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee == trampoline)
          ++base_trampoline_calls;
        if (callee->hasFnAttribute("omill.virtual_specialized"))
          ++specialized_calls;
        if (callee == trampoline || callee->hasFnAttribute("omill.virtual_specialized"))
          called_callees.insert(callee);
      }
    }
  }

  unsigned dispatch_calls = 0;
  unsigned direct_target_calls = 0;
  for (llvm::Function *callee : called_callees) {
    if (callee->hasFnAttribute("omill.virtual_specialized"))
      EXPECT_TRUE(
          callee->hasFnAttribute("omill.virtual_specialization.stack_facts"));
    for (auto &BB : *callee) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *target = CI->getCalledFunction();
        if (!target)
          continue;
        if (target->getName() == "__omill_dispatch_jump")
          ++dispatch_calls;
        if (target == target_a || target == target_b)
          ++direct_target_calls;
      }
    }
  }

  EXPECT_EQ(base_trampoline_calls, 0u);
  EXPECT_EQ(specialized_calls, 2u);
  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_target_calls, 2u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesLeafHelperNextPcPerCallsiteWithoutCrossCallerPhiPollution) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180005002", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180006002", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_write_next_pc_plus_two", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *scratch = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAdd(helper->getArg(2), B.getInt64(2));
    B.CreateStore(next_pc, scratch);
    auto *reloaded_next_pc = B.CreateLoad(i64_ty, scratch);
    B.CreateStore(reloaded_next_pc, helper->getArg(3));
    B.CreateRet(helper->getArg(0));
  }

  auto make_root = [&](llvm::StringRef name, uint64_t target_pc) {
    auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        name, *M);
    root->addFnAttr("omill.output_root");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *call = B.CreateCall(
        helper, {root->getArg(2), root->getArg(0), B.getInt64(target_pc - 2),
                 next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateRet(B.CreateCall(dispatch, {root->getArg(0), loaded_next_pc, call}));
    return root;
  };

  auto *root_a = make_root("sub_180008000", 0x180005002ULL);
  auto *root_b = make_root("sub_180008100", 0x180006002ULL);

  runPass(*M);

  auto count_calls = [](llvm::Function &F, llvm::Function *target) {
    unsigned dispatch_calls = 0;
    unsigned direct_calls = 0;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_jump")
          ++dispatch_calls;
        if (callee == target)
          ++direct_calls;
      }
    }
    return std::pair<unsigned, unsigned>(dispatch_calls, direct_calls);
  };

  auto [dispatch_a, direct_a] = count_calls(*root_a, target_a);
  auto [dispatch_b, direct_b] = count_calls(*root_b, target_b);
  EXPECT_EQ(dispatch_a, 0u);
  EXPECT_EQ(direct_a, 1u);
  EXPECT_EQ(dispatch_b, 0u);
  EXPECT_EQ(direct_b, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromSequentialLeafHelperVmMemoryReplay) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *read_mem_ty =
      llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180005220", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_push_then_pop_vm_stack_same_block", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, helper->getArg(1), B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {helper->getArg(0), new_sp, helper->getArg(3)});
    B.CreateStore(new_sp, sp_slot);
    auto *reloaded = B.CreateCall(read_mem, {helper->getArg(0), new_sp});
    B.CreateStore(reloaded, helper->getArg(2));
    B.CreateRet(next_memory);
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180005200", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    B.CreateCall(helper, {root->getArg(2), root->getArg(0), next_pc,
                          B.getInt64(0x180005220ULL)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateRet(B.CreateCall(dispatch,
                             {root->getArg(0), loaded_next_pc,
                              root->getArg(2)}));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromSequentialSingleBlockHandlerHelperChain) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *jmpi_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *read_mem_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  constexpr uint64_t kDelta = 0xF5DDULL;

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target_a = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180005720", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_a);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_a->getArg(0));
  }

  auto *target_b = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180006720", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target_b);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target_b->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_chain_push_imm", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(1),
                                B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(0), new_sp,
                                 push_helper->getArg(2)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_chain_pop_to_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded =
        B.CreateCall(read_mem, {pop_helper->getArg(0), pop_helper->getArg(3)});
    B.CreateStore(loaded, pop_helper->getArg(2));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *store_helper = llvm::Function::Create(
      store_ty, llvm::Function::ExternalLinkage, "helper_chain_store_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(store_helper->getArg(3), store_helper->getArg(2));
    B.CreateRet(store_helper->getArg(0));
  }

  auto *jmpi_helper = llvm::Function::Create(
      jmpi_ty, llvm::Function::ExternalLinkage, "helper_chain_jmpi", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jmpi_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jmpi_helper->getArg(2), jmpi_helper->getArg(3));
    B.CreateRet(jmpi_helper->getArg(0));
  }

  auto make_root = [&](llvm::StringRef name, uint64_t target_pc) {
    auto *root = llvm::Function::Create(lifted_ty, llvm::Function::ExternalLinkage,
                                        name, *M);
    root->addFnAttr("omill.output_root");
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *tmp = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    auto *mem1 = B.CreateCall(push_helper, {root->getArg(2), root->getArg(0),
                                            B.getInt64(target_pc + kDelta)});
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *mem2 = B.CreateCall(pop_helper,
                              {mem1, root->getArg(0), tmp, sp});
    auto *loaded = B.CreateLoad(i64_ty, tmp);
    auto *adjusted = B.CreateAdd(loaded, B.getInt64(-static_cast<int64_t>(kDelta)));
    auto *mem3 = B.CreateCall(store_helper,
                              {mem2, root->getArg(0), tmp, adjusted});
    auto *resolved = B.CreateLoad(i64_ty, tmp);
    auto *mem4 = B.CreateCall(jmpi_helper,
                              {mem3, root->getArg(0), resolved, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateRet(B.CreateCall(dispatch,
                             {root->getArg(0), loaded_next_pc, mem4}));
    return root;
  };

  auto *root_a = make_root("sub_180005700", 0x180005720ULL);
  auto *root_b = make_root("sub_180006700", 0x180006720ULL);

  runPass(*M);

  auto count_calls = [](llvm::Function &F, llvm::Function *target) {
    unsigned dispatch_calls = 0;
    unsigned direct_calls = 0;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        if (callee->getName() == "__omill_dispatch_jump")
          ++dispatch_calls;
        if (callee == target)
          ++direct_calls;
      }
    }
    return std::pair<unsigned, unsigned>(dispatch_calls, direct_calls);
  };

  auto [dispatch_a, direct_a] = count_calls(*root_a, target_a);
  auto [dispatch_b, direct_b] = count_calls(*root_b, target_b);
  EXPECT_EQ(dispatch_a, 0u);
  EXPECT_EQ(direct_a, 1u);
  EXPECT_EQ(dispatch_b, 0u);
  EXPECT_EQ(direct_b, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromSequentialLinearTwoBlockHandlerHelperChain) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *stack_array_ty = llvm::ArrayType::get(i64_ty, 2);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *push_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);
  auto *pop_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *store_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, ptr_ty, i64_ty}, false);
  auto *jmpi_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty}, false);
  auto *read_mem_ty = llvm::FunctionType::get(i64_ty, {ptr_ty, i64_ty}, false);
  auto *write_mem_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i64_ty}, false);

  constexpr uint64_t kDelta = 0xF5DDULL;

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);
  auto *read_mem = llvm::Function::Create(
      read_mem_ty, llvm::Function::ExternalLinkage, "__remill_read_memory_64",
      *M);
  auto *write_mem =
      llvm::Function::Create(write_mem_ty, llvm::Function::ExternalLinkage,
                             "__remill_write_memory_64", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180005920", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *push_helper = llvm::Function::Create(
      push_ty, llvm::Function::ExternalLinkage, "helper_two_block_push_imm", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", push_helper);
    llvm::IRBuilder<> B(entry);
    auto *sp_slot = B.CreateGEP(i8_ty, push_helper->getArg(1),
                                B.getInt64(0x908));
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *new_sp = B.CreateSub(sp, B.getInt64(8));
    auto *next_memory =
        B.CreateCall(write_mem, {push_helper->getArg(0), new_sp,
                                 push_helper->getArg(2)});
    B.CreateStore(new_sp, sp_slot);
    B.CreateRet(next_memory);
  }

  auto *pop_helper = llvm::Function::Create(
      pop_ty, llvm::Function::ExternalLinkage, "helper_two_block_pop_to_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", pop_helper);
    llvm::IRBuilder<> B(entry);
    auto *loaded =
        B.CreateCall(read_mem, {pop_helper->getArg(0), pop_helper->getArg(3)});
    B.CreateStore(loaded, pop_helper->getArg(2));
    B.CreateRet(pop_helper->getArg(0));
  }

  auto *store_helper = llvm::Function::Create(
      store_ty, llvm::Function::ExternalLinkage, "helper_two_block_store_tmp", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", store_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(store_helper->getArg(3), store_helper->getArg(2));
    B.CreateRet(store_helper->getArg(0));
  }

  auto *jmpi_helper = llvm::Function::Create(
      jmpi_ty, llvm::Function::ExternalLinkage, "helper_two_block_jmpi", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", jmpi_helper);
    llvm::IRBuilder<> B(entry);
    B.CreateStore(jmpi_helper->getArg(2), jmpi_helper->getArg(3));
    B.CreateRet(jmpi_helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180005900", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    auto *tail = llvm::BasicBlock::Create(Ctx, "tail", root);
    llvm::IRBuilder<> B(entry);
    auto *vm_stack = B.CreateAlloca(stack_array_ty, nullptr, "vm_stack");
    auto *stack_top = B.CreateGEP(stack_array_ty, vm_stack,
                                  {B.getInt64(0), B.getInt64(1)});
    auto *tmp = B.CreateAlloca(i64_ty, nullptr, "TMP");
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *sp_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x908));
    B.CreateStore(B.CreatePtrToInt(stack_top, i64_ty), sp_slot);
    auto *mem1 = B.CreateCall(push_helper, {root->getArg(2), root->getArg(0),
                                            B.getInt64(0x180005920ULL + kDelta)});
    auto *sp = B.CreateLoad(i64_ty, sp_slot);
    auto *mem2 = B.CreateCall(pop_helper, {mem1, root->getArg(0), tmp, sp});
    auto *loaded = B.CreateLoad(i64_ty, tmp);
    auto *adjusted = B.CreateAdd(loaded, B.getInt64(-static_cast<int64_t>(kDelta)));
    B.CreateCall(store_helper, {mem2, root->getArg(0), tmp, adjusted});
    B.CreateBr(tail);

    B.SetInsertPoint(tail);
    auto *resolved = B.CreateLoad(i64_ty, tmp);
    auto *mem4 = B.CreateCall(jmpi_helper,
                              {root->getArg(2), root->getArg(0), resolved, next_pc});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateRet(B.CreateCall(dispatch,
                             {root->getArg(0), loaded_next_pc, mem4}));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       SynthesizesLocalizedContinuationShimForSameHandlerLocalizedCallSite) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);
  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000f013", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000f000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    B.CreateCall(calli, {root->getArg(2), root->getArg(0),
                         B.getInt64(0x18000F100ULL), next_pc,
                         B.getInt64(0x18000F013ULL), return_pc});
    auto *saved_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *state_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8A8));
    B.CreateStore(saved_return_pc, state_slot);
    auto *tail = B.CreateCall(continuation, {root->getArg(0),
                                             B.getInt64(0x18000F013ULL),
                                             root->getArg(2)});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x2000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x18000F000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x18000F000ULL, image.data(), image.size(), false,
                /*executable=*/false);

  runPass(*M, std::move(map));

  auto *continuation_after = M->getFunction("blk_18000f013");
  ASSERT_NE(continuation_after, nullptr);
  EXPECT_FALSE(continuation_after->isDeclaration());
  EXPECT_EQ(continuation_after->getLinkage(),
            llvm::GlobalValue::InternalLinkage);
  EXPECT_TRUE(continuation_after->hasFnAttribute("omill.localized_continuation_shim"));
  EXPECT_TRUE(continuation_after->hasFnAttribute(llvm::Attribute::AlwaysInline));
  ASSERT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_disposition"));
  EXPECT_EQ(continuation_after
                ->getFnAttribute("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_call_reenter");
  EXPECT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_continuation_pc"));
  EXPECT_EQ(continuation_after
                ->getFnAttribute("omill.virtual_exit_continuation_pc")
                .getValueAsString(),
            "18000F013");
  EXPECT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_reenters_vm"));

  auto &entry = continuation_after->getEntryBlock();
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(entry.getTerminator());
  ASSERT_NE(ret, nullptr);
  ASSERT_NE(ret->getReturnValue(), nullptr);
  EXPECT_TRUE(llvm::isa<llvm::FreezeInst>(ret->getReturnValue()) ||
              ret->getReturnValue() == continuation_after->getArg(2));
}

TEST_F(VirtualCFGMaterializationTest,
       LeavesContinuationDeclarationForOpenResolvedCallSite) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *calli_ty = llvm::FunctionType::get(
      ptr_ty, {ptr_ty, ptr_ty, i64_ty, ptr_ty, i64_ty, ptr_ty}, false);

  auto *calli = llvm::Function::Create(
      calli_ty, llvm::Function::ExternalLinkage,
      "_ZN12_GLOBAL__N_14CALLI2InImEEEP6MemoryS4_R5StateT_3RnWImES2_S9_", *M);

  auto *call_target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180010080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", call_target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(call_target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180010013", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180010000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    auto *return_pc = B.CreateAlloca(i64_ty, nullptr, "RETURN_PC");
    auto *seeded_return_pc = B.CreateLoad(i64_ty, return_pc);
    auto *seeded_target = B.CreateAdd(seeded_return_pc, B.getInt64(0x6D));
    B.CreateStore(seeded_target, next_pc);
    auto *target_pc = B.CreateLoad(i64_ty, next_pc);
    auto *helper_return_pc = B.CreateLoad(i64_ty, return_pc);
    B.CreateCall(calli, {root->getArg(2), root->getArg(0), target_pc, next_pc,
                         helper_return_pc, return_pc});
    auto *call_result = B.CreateCall(
        call_target,
        {root->getArg(0), B.getInt64(0x180010080ULL), root->getArg(2)});
    auto *tail = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x180010013ULL), call_result});
    tail->setTailCallKind(llvm::CallInst::TCK_MustTail);
    B.CreateRet(tail);
  }

  std::vector<uint8_t> image(0x40000, 0x90);
  omill::BinaryMemoryMap map;
  map.setImageBase(0x180000000ULL);
  map.setImageSize(image.size());
  map.addRegion(0x180000000ULL, image.data(), image.size(), false);

  runPass(*M, std::move(map));

  auto *continuation_after = M->getFunction("blk_180010013");
  ASSERT_NE(continuation_after, nullptr);
  EXPECT_TRUE(continuation_after->isDeclaration());
  EXPECT_FALSE(
      continuation_after->hasFnAttribute("omill.localized_continuation_shim"));
  EXPECT_FALSE(
      continuation_after->hasFnAttribute(llvm::Attribute::AlwaysInline));
}

TEST_F(VirtualCFGMaterializationTest,
       RewritesDeclaredContinuationCallAndPreservesExitAttrs) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180030080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180030013", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180030000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *tail = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x180030080ULL), root->getArg(2)});
    tail->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_disposition",
        "vm_exit_native_call_reenter"));
    tail->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_continuation_pc", "180030013"));
    tail->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_continuation_vip", "180030013"));
    tail->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_native_target_pc", "180040000"));
    tail->addFnAttr(
        llvm::Attribute::get(Ctx, "omill.virtual_exit_reenters_vm", "1"));
    B.CreateRet(tail);
  }

  runPass(*M);

  llvm::CallInst *direct_call = nullptr;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI || CI->getCalledFunction() != target)
        continue;
      direct_call = CI;
    }
  }

  ASSERT_NE(direct_call, nullptr);
  EXPECT_EQ(M->getFunction("blk_180030013"), continuation);
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_call_reenter");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_continuation_pc"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_continuation_pc")
                .getValueAsString(),
            "180030013");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_continuation_vip"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_continuation_vip")
                .getValueAsString(),
            "180030013");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_native_target_pc"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_native_target_pc")
                .getValueAsString(),
            "180040000");
  EXPECT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_reenters_vm"));
}

TEST_F(VirtualCFGMaterializationTest,
       SynthesizesContinuationShimForNullMemoryContinuationCall) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_18000f005", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000f000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *tail = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x18000F005ULL),
         llvm::ConstantPointerNull::get(ptr_ty)});
    tail->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_disposition",
        "vm_exit_native_exec_unknown_return"));
    tail->addFnAttr(llvm::Attribute::get(
        Ctx, "omill.virtual_exit_native_target_pc", "180020100"));
    tail->addFnAttr(
        llvm::Attribute::get(Ctx, "omill.virtual_exit_partial", "1"));
    B.CreateRet(tail);
  }

  runPass(*M);

  auto *continuation_after = M->getFunction("blk_18000f005");
  ASSERT_NE(continuation_after, nullptr);
  EXPECT_FALSE(continuation_after->isDeclaration());
  EXPECT_EQ(continuation_after->getLinkage(),
            llvm::GlobalValue::InternalLinkage);
  EXPECT_TRUE(
      continuation_after->hasFnAttribute("omill.localized_continuation_shim"));
  EXPECT_TRUE(
      continuation_after->hasFnAttribute(llvm::Attribute::AlwaysInline));
  ASSERT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_disposition"));
  EXPECT_EQ(continuation_after
                ->getFnAttribute("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_exec_unknown_return");
  EXPECT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_continuation_pc"));
  EXPECT_EQ(continuation_after
                ->getFnAttribute("omill.virtual_exit_continuation_pc")
                .getValueAsString(),
            "18000F005");
  EXPECT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_native_target_pc"));
  EXPECT_EQ(continuation_after
                ->getFnAttribute("omill.virtual_exit_native_target_pc")
                .getValueAsString(),
            "180020100");
  EXPECT_TRUE(
      continuation_after->hasFnAttribute("omill.virtual_exit_partial"));
}

TEST_F(VirtualCFGMaterializationTest,
       RewritesDeclaredContinuationCallUsingCalleeExitAttrsWhenCallsiteIsBare) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *target = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "sub_180031080", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *continuation = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "blk_180031013", *M);
  continuation->addFnAttr("omill.virtual_exit_disposition",
                          "vm_exit_native_call_reenter");
  continuation->addFnAttr("omill.virtual_exit_continuation_pc", "180031013");
  continuation->addFnAttr("omill.virtual_exit_continuation_vip", "180031013");
  continuation->addFnAttr("omill.virtual_exit_native_target_pc", "180041000");
  continuation->addFnAttr("omill.virtual_exit_reenters_vm", "1");

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180031000", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *tail = B.CreateCall(
        continuation,
        {root->getArg(0), B.getInt64(0x180031080ULL), root->getArg(2)});
    B.CreateRet(tail);
  }

  runPass(*M);

  llvm::CallInst *direct_call = nullptr;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI || CI->getCalledFunction() != target)
        continue;
      direct_call = CI;
    }
  }

  ASSERT_NE(direct_call, nullptr);
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_disposition"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_disposition")
                .getValueAsString(),
            "vm_exit_native_call_reenter");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_continuation_pc"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_continuation_pc")
                .getValueAsString(),
            "180031013");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_continuation_vip"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_continuation_vip")
                .getValueAsString(),
            "180031013");
  ASSERT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_native_target_pc"));
  EXPECT_EQ(direct_call->getFnAttr("omill.virtual_exit_native_target_pc")
                .getValueAsString(),
            "180041000");
  EXPECT_TRUE(direct_call->hasFnAttr("omill.virtual_exit_reenters_vm"));
}

TEST_F(VirtualCFGMaterializationTest,
       FallsBackFromUnsupportedLeafHelperReplayDuringMaterialization) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);
  auto *helper_ty =
      llvm::FunctionType::get(ptr_ty, {ptr_ty, ptr_ty, i64_ty}, false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_180005420", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *helper = llvm::Function::Create(
      helper_ty, llvm::Function::ExternalLinkage,
      "helper_store_next_pc_with_dead_mul", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", helper);
    llvm::IRBuilder<> B(entry);
    (void) B.CreateMul(helper->getArg(2), B.getInt64(3), "dead_mul");
    B.CreateStore(helper->getArg(2), helper->getArg(1));
    B.CreateRet(helper->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180005400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *next_pc = B.CreateAlloca(i64_ty, nullptr, "NEXT_PC");
    B.CreateCall(helper,
                 {root->getArg(2), next_pc, B.getInt64(0x180005420ULL)});
    auto *loaded_next_pc = B.CreateLoad(i64_ty, next_pc);
    B.CreateRet(B.CreateCall(dispatch,
                             {root->getArg(0), loaded_next_pc,
                              root->getArg(2)}));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest, LeavesCleanupScopeDisabledForOpenRootSlice) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_180008200", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *dynamic_target = B.CreateLoad(i64_ty, root->getArg(0), "next_pc");
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), dynamic_target,
                                root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  auto *scope_flag = M->getModuleFlag("omill.closed_root_slice_scope");
  ASSERT_NE(scope_flag, nullptr);
  auto *scope_ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(scope_flag);
  ASSERT_NE(scope_ci, nullptr);
  EXPECT_EQ(scope_ci->getZExtValue(), 0u);
  EXPECT_FALSE(root->hasFnAttribute("omill.closed_root_slice"));
  EXPECT_FALSE(root->hasFnAttribute("omill.closed_root_slice_root"));
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromRecursiveSlotAliases) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "sub_18000a120", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000a100", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_y = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *slot_x = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x110));
    B.CreateStore(B.getInt64(0x18000A120ULL), slot_y);
    auto *value_y = B.CreateLoad(i64_ty, slot_y);
    B.CreateStore(value_y, slot_x);
    auto *target_pc = B.CreateLoad(i64_ty, slot_x);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(
    VirtualCFGMaterializationTest,
    MaterializesDispatchInAdjacentWrapperOutsideForwardReachabilityScope) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000b120", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000b000", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(target, {root->getArg(0), B.getInt64(0x18000B120ULL),
                                       root->getArg(2)});
    B.CreateRet(call);
  }

  auto *wrapper = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "sub_18000b0f0", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", wrapper);
    llvm::IRBuilder<> B(entry);
    auto *call = B.CreateCall(dispatch, {wrapper->getArg(0),
                                         B.getInt64(0x18000B120ULL),
                                         wrapper->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned wrapper_dispatch_calls = 0;
  unsigned wrapper_direct_calls = 0;
  for (auto &BB : *wrapper) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++wrapper_dispatch_calls;
      if (callee == target)
        ++wrapper_direct_calls;
    }
  }

  EXPECT_EQ(wrapper_dispatch_calls, 0u);
  EXPECT_EQ(wrapper_direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       LeavesUnsupportedSlotProvenanceDispatchUnchanged) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000a200", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot_y = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x108));
    auto *slot_x = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x110));
    auto *value_y = B.CreateLoad(i64_ty, slot_y);
    auto *value_x = B.CreateXor(value_y, B.getInt64(0x20));
    B.CreateStore(value_x, slot_x);
    auto *target_pc = B.CreateLoad(i64_ty, slot_x);
    B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(root->getArg(0));
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (callee && callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromBooleanFlagSlotChoices) {
  auto M = createModule();
  addMinimalX86FlagStateTypes(*M);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_call", *M);

  auto *target0 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000c100", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target0);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target0->getArg(0));
  }

  auto *target1 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000c101", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target1);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target1->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000c080", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *cf_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x811));
    auto *cf = B.CreateLoad(i8_ty, cf_slot);
    auto *cf64 = B.CreateZExt(cf, i64_ty);
    auto *target_pc = B.CreateAdd(B.getInt64(0x18000C100ULL), cf64);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_target0_calls = 0;
  unsigned direct_target1_calls = 0;
  unsigned switch_count = 0;
  for (auto &BB : *root) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_count;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_call")
        ++dispatch_calls;
      if (callee == target0)
        ++direct_target0_calls;
      if (callee == target1)
        ++direct_target1_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_target0_calls, 1u);
  EXPECT_EQ(direct_target1_calls, 1u);
  EXPECT_EQ(switch_count, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchFromSingleBitMaskedSlotChoices) {
  auto M = createModule();
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target0 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000d300", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target0);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target0->getArg(0));
  }

  auto *target1 = llvm::Function::Create(lifted_ty,
                                         llvm::Function::ExternalLinkage,
                                         "blk_18000d301", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target1);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target1->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d280", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x8F8));
    auto *value = B.CreateLoad(i64_ty, slot);
    auto *shifted = B.CreateLShr(value, B.getInt64(62));
    auto *bit = B.CreateAnd(B.CreateTrunc(shifted, i8_ty), B.getInt8(1));
    auto *bit64 = B.CreateZExt(bit, i64_ty);
    auto *target_pc = B.CreateAdd(B.getInt64(0x18000D300ULL), bit64);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_target0_calls = 0;
  unsigned direct_target1_calls = 0;
  unsigned switch_count = 0;
  for (auto &BB : *root) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_count;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target0)
        ++direct_target0_calls;
      if (callee == target1)
        ++direct_target1_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_target0_calls, 1u);
  EXPECT_EQ(direct_target1_calls, 1u);
  EXPECT_EQ(switch_count, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       CollapsesDuplicateCanonicalizedSwitchTargetsToDirectCall) {
  auto M = createModule();
  addMinimalX86FlagStateTypes(*M);
  auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000d500", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *boundary0 = llvm::Function::Create(lifted_ty,
                                           llvm::Function::ExternalLinkage,
                                           "vm_entry_18000d300", *M);
  boundary0->addFnAttr("omill.protection_boundary");
  boundary0->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary0->addFnAttr("omill.boundary_entry_va", "18000D300");
  boundary0->addFnAttr("omill.boundary_target_va", "18000D500");

  auto *boundary1 = llvm::Function::Create(lifted_ty,
                                           llvm::Function::ExternalLinkage,
                                           "vm_entry_18000d301", *M);
  boundary1->addFnAttr("omill.protection_boundary");
  boundary1->addFnAttr("omill.boundary_kind", "vm_entry_stub");
  boundary1->addFnAttr("omill.boundary_entry_va", "18000D301");
  boundary1->addFnAttr("omill.boundary_target_va", "18000D500");

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000d280", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *cf_slot = B.CreateGEP(i8_ty, root->getArg(0), B.getInt64(0x811));
    auto *cf = B.CreateLoad(i8_ty, cf_slot);
    auto *cf64 = B.CreateZExt(cf, i64_ty);
    auto *target_pc = B.CreateAdd(B.getInt64(0x18000D300ULL), cf64);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), target_pc, root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_target_calls = 0;
  unsigned boundary_calls = 0;
  unsigned switch_count = 0;
  for (auto &BB : *root) {
    if (llvm::isa<llvm::SwitchInst>(BB.getTerminator()))
      ++switch_count;
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_target_calls;
      if (callee == boundary0 || callee == boundary1)
        ++boundary_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_target_calls, 1u);
  EXPECT_EQ(boundary_calls, 0u);
  EXPECT_EQ(switch_count, 0u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchToNearbyRecoveredLiftedEntry) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000e240", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e200", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x18000E245ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchToForwardNearbyRecoveredLiftedEntry) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000e348", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e300", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x18000E345ULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

TEST_F(VirtualCFGMaterializationTest,
       MaterializesDispatchToExtendedNearbyRecoveredLiftedEntry) {
  auto M = createModule();
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
  auto *lifted_ty = llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty},
                                            false);

  auto *dispatch = llvm::Function::Create(
      lifted_ty, llvm::Function::ExternalLinkage, "__omill_dispatch_jump", *M);

  auto *target = llvm::Function::Create(lifted_ty,
                                        llvm::Function::ExternalLinkage,
                                        "blk_18000e440", *M);
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", target);
    llvm::IRBuilder<> B(entry);
    B.CreateRet(target->getArg(0));
  }

  auto *root = llvm::Function::Create(lifted_ty,
                                      llvm::Function::ExternalLinkage,
                                      "sub_18000e400", *M);
  root->addFnAttr("omill.output_root");
  {
    auto *entry = llvm::BasicBlock::Create(Ctx, "entry", root);
    llvm::IRBuilder<> B(entry);
    auto *call =
        B.CreateCall(dispatch, {root->getArg(0), B.getInt64(0x18000E45BULL),
                                root->getArg(2)});
    B.CreateRet(call);
  }

  runPass(*M);

  unsigned dispatch_calls = 0;
  unsigned direct_calls = 0;
  for (auto &BB : *root) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI)
        continue;
      auto *callee = CI->getCalledFunction();
      if (!callee)
        continue;
      if (callee->getName() == "__omill_dispatch_jump")
        ++dispatch_calls;
      if (callee == target)
        ++direct_calls;
    }
  }

  EXPECT_EQ(dispatch_calls, 0u);
  EXPECT_EQ(direct_calls, 1u);
}

}  // namespace
