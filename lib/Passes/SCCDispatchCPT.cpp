#include "omill/Passes/SCCDispatchCPT.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/Analysis/DomTreeUpdater.h>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Dominators.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/InlineAsm.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/PassManager.h>
#include <llvm/Transforms/IPO/AlwaysInliner.h>
#include <llvm/Transforms/IPO/GlobalDCE.h>
#include <llvm/Transforms/Scalar/ADCE.h>
#include <llvm/Transforms/Scalar/DeadStoreElimination.h>
#include <llvm/Transforms/Scalar/GVN.h>
#include <llvm/Transforms/InstCombine/InstCombine.h>
#include <llvm/Transforms/Scalar/SimplifyCFG.h>
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include <llvm/Transforms/Utils/Local.h>
#include <llvm/Transforms/Utils/Mem2Reg.h>
#include <llvm/Transforms/Utils/PromoteMemToReg.h>

#include <cstdlib>

namespace omill {

llvm::PreservedAnalyses SCCDispatchCPTPass::run(llvm::Module &M,
                                                llvm::ModuleAnalysisManager &MAM) {
  auto *scc_fn = M.getFunction("scc_dispatch");
  if (!scc_fn || scc_fn->isDeclaration())
    return llvm::PreservedAnalyses::all();

  // Find the dispatch block (has a SwitchInst with many cases).
  llvm::SwitchInst *dispatch_switch = nullptr;
  llvm::BasicBlock *dispatch_bb = nullptr;
  for (auto &BB : *scc_fn) {
    if (auto *SW = llvm::dyn_cast<llvm::SwitchInst>(BB.getTerminator())) {
      if (SW->getNumCases() > 10) {
        dispatch_switch = SW;
        dispatch_bb = &BB;
        break;
      }
    }
  }

  if (!dispatch_switch)
    return llvm::PreservedAnalyses::all();

  // Collect recursive scc_dispatch calls with constant PC.
  llvm::SmallVector<llvm::CallInst *, 16> recursive_calls;
  for (auto &BB : *scc_fn) {
    for (auto &I : BB) {
      auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!CI || CI->getCalledFunction() != scc_fn)
        continue;
      if (llvm::isa<llvm::ConstantInt>(CI->getArgOperand(1)))
        recursive_calls.push_back(CI);
    }
  }

  if (recursive_calls.empty())
    return llvm::PreservedAnalyses::all();

  // Step 1: Demote all dispatch PHIs to allocas.
  llvm::SmallVector<llvm::PHINode *, 64> dispatch_phis;
  for (auto &I : *dispatch_bb) {
    auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
    if (!phi)
      break;
    dispatch_phis.push_back(phi);
  }

  for (auto *phi : dispatch_phis)
    llvm::DemotePHIToStack(phi);

  // Re-find the switch (PHI demotion doesn't move it).
  dispatch_switch = llvm::cast<llvm::SwitchInst>(dispatch_bb->getTerminator());

  // Step 2: Create cont_id alloca in entry block.
  auto &entry_bb = scc_fn->getEntryBlock();
  llvm::IRBuilder<> EntryBuilder(&*entry_bb.getFirstInsertionPt());
  auto *cont_id_alloca = EntryBuilder.CreateAlloca(
      EntryBuilder.getInt32Ty(), nullptr, "cont_id");
  EntryBuilder.CreateStore(EntryBuilder.getInt32(0), cont_id_alloca);

  auto *state_arg = scc_fn->getArg(0);

  // Step 3: Split dispatch_bb to add cont_id check before switch.
  auto *cont_check_bb = dispatch_bb->splitBasicBlock(
      dispatch_switch->getIterator(), "dispatch.cont_check");
  // dispatch_bb now ends with br to cont_check_bb.

  // Replace the unconditional br with cont_id check.
  dispatch_bb->getTerminator()->eraseFromParent();
  llvm::IRBuilder<> DispBuilder(dispatch_bb);
  auto *cont_val = DispBuilder.CreateLoad(
      DispBuilder.getInt32Ty(), cont_id_alloca, "cont_val");
  DispBuilder.CreateStore(DispBuilder.getInt32(0), cont_id_alloca);
  auto *is_cont = DispBuilder.CreateICmpNE(
      cont_val, DispBuilder.getInt32(0), "is_continuation");

  auto *cont_dispatch_bb = llvm::BasicBlock::Create(
      scc_fn->getContext(), "dispatch.continuations", scc_fn);
  DispBuilder.CreateCondBr(is_cont, cont_dispatch_bb, cont_check_bb);

  // Build continuation switch (populated below).
  llvm::IRBuilder<> ContBuilder(cont_dispatch_bb);
  auto *unreachable_bb = llvm::BasicBlock::Create(
      scc_fn->getContext(), "cont.unreachable", scc_fn);
  llvm::IRBuilder<> UB(unreachable_bb);
  UB.CreateUnreachable();
  auto *cont_switch = ContBuilder.CreateSwitch(
      cont_val, unreachable_bb,
      static_cast<unsigned>(recursive_calls.size()));

  // Step 4: Transform each recursive call.
  unsigned cont_id_counter = 0;
  unsigned transformed = 0;
  for (auto *CI : recursive_calls) {
    ++cont_id_counter;

    auto *call_bb = CI->getParent();
    auto *const_pc = llvm::cast<llvm::ConstantInt>(CI->getArgOperand(1));

    auto *continuation_bb = call_bb->splitBasicBlock(
        CI->getIterator(), "cont." + llvm::Twine(cont_id_counter));

    call_bb->getTerminator()->eraseFromParent();

    llvm::IRBuilder<> BeforeBuilder(call_bb);
    BeforeBuilder.CreateStore(
        BeforeBuilder.getInt32(cont_id_counter), cont_id_alloca);
    auto *pc_gep = BeforeBuilder.CreateGEP(
        BeforeBuilder.getInt8Ty(), state_arg,
        BeforeBuilder.getInt64(2472), "pc_ptr");
    BeforeBuilder.CreateStore(const_pc, pc_gep);
    BeforeBuilder.CreateBr(dispatch_bb);

    auto *mem_arg = scc_fn->getArg(2);
    CI->replaceAllUsesWith(mem_arg);
    CI->eraseFromParent();

    cont_switch->addCase(
        llvm::ConstantInt::get(
            llvm::Type::getInt32Ty(scc_fn->getContext()), cont_id_counter),
        continuation_bb);

    ++transformed;
  }

  // Fix dominance: demoted PHI loads in dispatch_bb are used by continuation
  // blocks that aren't dominated by dispatch_bb.  Insert fresh loads.
  for (auto &I : *dispatch_bb) {
    auto *load = llvm::dyn_cast<llvm::LoadInst>(&I);
    if (!load)
      continue;
    auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(load->getPointerOperand());
    if (!alloca)
      continue;

    llvm::SmallVector<llvm::Use *, 8> to_fix;
    for (auto &U : load->uses()) {
      auto *user = llvm::cast<llvm::Instruction>(U.getUser());
      auto *user_bb = user->getParent();
      if (user_bb != dispatch_bb && user_bb != cont_check_bb)
        to_fix.push_back(&U);
    }

    if (to_fix.empty())
      continue;

    llvm::DenseMap<llvm::BasicBlock *, llvm::LoadInst *> block_loads;
    for (auto *U : to_fix) {
      auto *user = llvm::cast<llvm::Instruction>(U->getUser());
      auto *user_bb = user->getParent();
      auto &cached = block_loads[user_bb];
      if (!cached) {
        auto insert_pt = user_bb->getFirstNonPHIIt();
        cached = new llvm::LoadInst(
            load->getType(), alloca,
            load->getName() + ".cont",
            &*insert_pt);
      }
      U->set(cached);
    }
  }

  if (std::getenv("OMILL_DEBUG_CPT") != nullptr)
    llvm::errs() << "[cpt] transformed " << transformed
                 << " recursive scc_dispatch calls into "
                 << "continuation-passing dispatches\n";

  // Fix dominance violations: demote violating instructions, then re-promote.
  {
    llvm::DominatorTree DT(*scc_fn);
    llvm::SmallVector<llvm::Instruction *, 64> to_demote;
    for (auto &BB : *scc_fn) {
      for (auto &I : BB) {
        if (I.use_empty() || llvm::isa<llvm::AllocaInst>(&I))
          continue;
        for (auto &U : I.uses()) {
          if (!DT.dominates(&I, U)) {
            to_demote.push_back(&I);
            break;
          }
        }
      }
    }
    if (!to_demote.empty()) {
      llvm::SmallVector<llvm::AllocaInst *, 64> allocs;
      for (auto *I : to_demote) {
        if (auto *phi = llvm::dyn_cast<llvm::PHINode>(I))
          allocs.push_back(llvm::DemotePHIToStack(phi));
        else
          allocs.push_back(llvm::DemoteRegToStack(*I));
      }
      DT.recalculate(*scc_fn);
      llvm::SmallVector<llvm::AllocaInst *, 64> promotable;
      for (auto *A : allocs)
        if (A && llvm::isAllocaPromotable(A))
          promotable.push_back(A);
      if (!promotable.empty())
        llvm::PromoteMemToReg(promotable, DT);
    }
  }

  // Replace undef PHI values from entry with freeze(undef).
  for (auto &BB : *scc_fn) {
    for (auto &I : BB) {
      auto *phi = llvm::dyn_cast<llvm::PHINode>(&I);
      if (!phi)
        break;
      for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
        if (llvm::isa<llvm::UndefValue>(phi->getIncomingValue(i))) {
          auto *freeze = new llvm::FreezeInst(
              phi->getIncomingValue(i), "frozen",
              phi->getIncomingBlock(i)->getTerminator()->getIterator());
          phi->setIncomingValue(i, freeze);
        }
      }
    }
  }

  // Inline scc_dispatch into callers now that it has no recursive self-calls.
  scc_fn->addFnAttr(llvm::Attribute::AlwaysInline);
  if (scc_fn->hasFnAttribute(llvm::Attribute::NoInline))
    scc_fn->removeFnAttr(llvm::Attribute::NoInline);

  // Clean up.
  MAM.invalidate(M, llvm::PreservedAnalyses::none());
  llvm::ModulePassManager CleanMPM;
  CleanMPM.addPass(llvm::AlwaysInlinerPass());

  // Fix output roots: replace unreachable with ret, and pin State arg.
  for (auto &F : M) {
    if (F.isDeclaration() || !F.getName().starts_with("sub_"))
      continue;
    for (auto &BB : F) {
      if (auto *UI = llvm::dyn_cast<llvm::UnreachableInst>(BB.getTerminator())) {
        llvm::IRBuilder<> B(UI);
        B.CreateRet(F.getArg(2));
        UI->eraseFromParent();
      }
    }
    auto *asm_ty = llvm::FunctionType::get(
        llvm::Type::getVoidTy(F.getContext()),
        {F.getArg(0)->getType()}, false);
    auto *pin_asm = llvm::InlineAsm::get(
        asm_ty, "", "r,~{memory}", /*hasSideEffects=*/true);
    for (auto &BB : F) {
      if (auto *RI = llvm::dyn_cast<llvm::ReturnInst>(BB.getTerminator())) {
        llvm::IRBuilder<> B(RI);
        B.CreateCall(asm_ty, pin_asm, {F.getArg(0)});
      }
    }
  }

  CleanMPM.addPass(llvm::GlobalDCEPass());
  {
    llvm::FunctionPassManager CleanFPM;
    CleanFPM.addPass(llvm::SimplifyCFGPass());
    CleanFPM.addPass(llvm::InstCombinePass());
    CleanFPM.addPass(llvm::GVNPass());
    CleanFPM.addPass(llvm::DSEPass());
    CleanFPM.addPass(llvm::ADCEPass());
    CleanFPM.addPass(llvm::SimplifyCFGPass());
    CleanMPM.addPass(llvm::createModuleToFunctionPassAdaptor(std::move(CleanFPM)));
  }
  CleanMPM.run(M, MAM);
  MAM.invalidate(M, llvm::PreservedAnalyses::none());

  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
