#include "omill/Analysis/RemillStateVariableSolver.h"

#include <algorithm>
#include <memory>
#include <optional>

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Analysis/CGSCCPassManager.h"
#include "llvm/Analysis/LoopAnalysisManager.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Transforms/InstCombine/InstCombine.h"
#include "llvm/Transforms/Scalar/EarlyCSE.h"
#include "llvm/Transforms/Scalar/GVN.h"
#include "llvm/Transforms/Scalar/SCCP.h"
#include "llvm/Transforms/Scalar/SimplifyCFG.h"
#include "llvm/Transforms/Scalar/SROA.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "omill/Devirtualization/ExecutableTargetFact.h"
#include "omill/Omill.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {
namespace {

constexpr unsigned kMaxEvalDepth = 48;
constexpr size_t kMaxSolvedValues = 32;
constexpr const char *kSolvedTargetSetMetadata = "omill.solved_target_pcs";
constexpr const char *kSolvedBranchTakenMetadata = "omill.solved_branch_taken";

template <typename T>
static void PushUnique(llvm::SmallVectorImpl<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

static uint64_t maskToWidth(uint64_t value, unsigned bit_width) {
  if (bit_width == 0 || bit_width >= 64) {
    return value;
  }
  return value & ((1ULL << bit_width) - 1ULL);
}

static uint64_t signExtendTo64(uint64_t value, unsigned bit_width) {
  if (bit_width == 0 || bit_width >= 64) {
    return value;
  }
  const uint64_t sign_bit = 1ULL << (bit_width - 1U);
  const uint64_t mask = (1ULL << bit_width) - 1ULL;
  uint64_t out = value & mask;
  if (out & sign_bit) {
    out |= ~mask;
  }
  return out;
}

struct SolverSite {
  enum class Kind : uint8_t {
    kUnknown = 0,
    kDispatchJump,
    kDispatchCall,
    kConditionalBranch,
  };

  Kind kind = Kind::kUnknown;
  llvm::Instruction *inst = nullptr;
};

static bool IsDispatchCall(const llvm::CallBase &call,
                           SolverSite::Kind &kind_out) {
  auto *callee = call.getCalledFunction();
  if (!callee) {
    return false;
  }
  const auto name = callee->getName();
  if (name == "__remill_jump" || name == "__omill_dispatch_jump") {
    kind_out = SolverSite::Kind::kDispatchJump;
    return true;
  }
  if (name == "__remill_function_call" || name == "__omill_dispatch_call") {
    kind_out = SolverSite::Kind::kDispatchCall;
    return true;
  }
  return false;
}

static SolverSite findControlTransferSite(llvm::Function &F, uint64_t control_pc) {
  auto scan_block = [&](llvm::BasicBlock &BB) {
    SolverSite site;
    for (auto &I : BB) {
      if (auto *call = llvm::dyn_cast<llvm::CallBase>(&I)) {
        SolverSite::Kind kind = SolverSite::Kind::kUnknown;
        if (IsDispatchCall(*call, kind)) {
          site.kind = kind;
          site.inst = call;
          return site;
        }
      }
    }
    if (auto *branch = llvm::dyn_cast<llvm::BranchInst>(BB.getTerminator());
        branch && branch->isConditional()) {
      site.kind = SolverSite::Kind::kConditionalBranch;
      site.inst = branch;
    }
    return site;
  };

  auto *named_block = findBlockForPC(F, control_pc);
  if (!named_block) {
    auto pc_map = collectBlockPCMap(F);
    auto it = pc_map.find(control_pc);
    if (it != pc_map.end()) {
      named_block = it->second;
    }
  }
  if (named_block) {
    auto site = scan_block(*named_block);
    if (site.inst) {
      return site;
    }
  }

  const uint64_t function_pc = extractStructuralCodeTargetPC(F);
  if (function_pc == control_pc || extractEntryVA(F.getName()) == control_pc ||
      extractBlockPC(F.getName()) == control_pc) {
    for (auto &BB : F) {
      auto site = scan_block(BB);
      if (site.inst) {
        return site;
      }
    }
  }

  return {};
}

static std::optional<uint64_t> extractTransferTargetFromBlock(
    llvm::BasicBlock *bb) {
  if (!bb) {
    return std::nullopt;
  }
  for (auto &I : *bb) {
    auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
    if (!call) {
      continue;
    }
    if (call->arg_size() >= 2) {
      if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(call->getArgOperand(1))) {
        return ci->getZExtValue();
      }
    }
    if (auto *callee = call->getCalledFunction()) {
      if (auto target = extractStructuralCodeTargetPC(*callee)) {
        return target;
      }
    }
  }
  return std::nullopt;
}

using IntSet = llvm::SmallVector<uint64_t, 8>;

struct SolverEvalContext {
  llvm::Function &function;
  llvm::Argument *pc_arg = nullptr;
  uint64_t entry_pc = 0;
  StateFieldMap field_map;
  llvm::MemorySSA *memory_ssa = nullptr;

  explicit SolverEvalContext(llvm::Function &F)
      : function(F),
        pc_arg(F.arg_size() > 1 ? llvm::dyn_cast<llvm::Argument>(F.getArg(1))
                                : nullptr),
        entry_pc(extractStructuralCodeTargetPC(F)),
        field_map(*F.getParent()) {}
};

static bool evalConcreteIntegers(
    llvm::Value *V, SolverEvalContext &ctx,
    llvm::DenseMap<llvm::Value *, IntSet> &memo,
    llvm::SmallPtrSet<llvm::Value *, 32> &in_progress, unsigned depth,
    IntSet &out);

static bool evalMemoryAccessForField(
    llvm::MemoryAccess *access, const StateField &field, SolverEvalContext &ctx,
    llvm::DenseMap<llvm::Value *, IntSet> &memo,
    llvm::SmallPtrSet<llvm::Value *, 32> &in_progress, unsigned depth,
    llvm::SmallPtrSet<llvm::MemoryAccess *, 16> &visited, IntSet &out) {
  if (!access || visited.contains(access) || depth > kMaxEvalDepth)
    return false;
  visited.insert(access);

  if (ctx.memory_ssa && access == ctx.memory_ssa->getLiveOnEntryDef())
    return false;

  if (auto *phi = llvm::dyn_cast<llvm::MemoryPhi>(access)) {
    bool resolved = false;
    for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
      IntSet incoming;
      if (!evalMemoryAccessForField(phi->getIncomingValue(i), field, ctx, memo,
                                    in_progress, depth + 1, visited,
                                    incoming)) {
        continue;
      }
      resolved = true;
      for (uint64_t value : incoming) {
        PushUnique(out, value);
        if (out.size() >= kMaxSolvedValues)
          return true;
      }
    }
    return resolved;
  }

  if (auto *use = llvm::dyn_cast<llvm::MemoryUse>(access)) {
    return evalMemoryAccessForField(use->getDefiningAccess(), field, ctx, memo,
                                    in_progress, depth + 1, visited, out);
  }

  auto *def = llvm::dyn_cast<llvm::MemoryDef>(access);
  if (!def)
    return false;

  if (auto *inst = def->getMemoryInst()) {
    if (auto *store = llvm::dyn_cast<llvm::StoreInst>(inst)) {
      if (auto resolved = ctx.field_map.resolvePointer(store->getPointerOperand());
          resolved && resolved->offset == field.offset) {
        return evalConcreteIntegers(store->getValueOperand(), ctx, memo,
                                    in_progress, depth + 1, out);
      }
    }
  }

  return evalMemoryAccessForField(def->getDefiningAccess(), field, ctx, memo,
                                  in_progress, depth + 1, visited, out);
}

static bool solveLoadWithMemorySSA(
    llvm::LoadInst *load, SolverEvalContext &ctx,
    llvm::DenseMap<llvm::Value *, IntSet> &memo,
    llvm::SmallPtrSet<llvm::Value *, 32> &in_progress, unsigned depth,
    IntSet &out) {
  if (!ctx.memory_ssa || !load)
    return false;
  auto field = ctx.field_map.resolvePointer(load->getPointerOperand());
  if (!field)
    return false;
  auto *access = ctx.memory_ssa->getMemoryAccess(load);
  if (!access)
    return false;
  auto *clobber = ctx.memory_ssa->getWalker()->getClobberingMemoryAccess(access);
  if (!clobber)
    return false;
  llvm::SmallPtrSet<llvm::MemoryAccess *, 16> visited;
  return evalMemoryAccessForField(clobber, *field, ctx, memo, in_progress,
                                  depth + 1, visited, out);
}

static bool evalConcreteIntegers(
    llvm::Value *V, SolverEvalContext &ctx,
    llvm::DenseMap<llvm::Value *, IntSet> &memo,
    llvm::SmallPtrSet<llvm::Value *, 32> &in_progress, unsigned depth,
    IntSet &out) {
  if (!V || depth > kMaxEvalDepth) {
    return false;
  }

  if (auto it = memo.find(V); it != memo.end()) {
    out = it->second;
    return !out.empty();
  }

  if (in_progress.contains(V)) {
    return false;
  }
  in_progress.insert(V);

  const unsigned bit_width =
      V->getType()->isIntegerTy() ? V->getType()->getIntegerBitWidth() : 64;
  IntSet values;

  if (V == ctx.pc_arg) {
    PushUnique(values, maskToWidth(ctx.entry_pc, bit_width));
  } else if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    PushUnique(values, maskToWidth(CI->getZExtValue(), bit_width));
  } else if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(V)) {
    solveLoadWithMemorySSA(LI, ctx, memo, in_progress, depth, values);
  } else if (auto *PN = llvm::dyn_cast<llvm::PHINode>(V)) {
    for (unsigned i = 0; i < PN->getNumIncomingValues(); ++i) {
      IntSet incoming;
      if (!evalConcreteIntegers(PN->getIncomingValue(i), ctx, memo,
                                in_progress, depth + 1, incoming)) {
        continue;
      }
      for (uint64_t value : incoming) {
        PushUnique(values, maskToWidth(value, bit_width));
        if (values.size() >= kMaxSolvedValues) {
          break;
        }
      }
      if (values.size() >= kMaxSolvedValues) {
        break;
      }
    }
  } else if (auto *SI = llvm::dyn_cast<llvm::SelectInst>(V)) {
    IntSet cond_values;
    if (evalConcreteIntegers(SI->getCondition(), ctx, memo,
                             in_progress, depth + 1, cond_values)) {
      const bool maybe_true =
          std::find_if(cond_values.begin(), cond_values.end(),
                       [](uint64_t value) { return value != 0; }) !=
          cond_values.end();
      const bool maybe_false =
          std::find(cond_values.begin(), cond_values.end(), 0) !=
          cond_values.end();
      if (maybe_true) {
        IntSet true_values;
        if (evalConcreteIntegers(SI->getTrueValue(), ctx, memo,
                                 in_progress, depth + 1, true_values)) {
          for (uint64_t value : true_values) {
            PushUnique(values, maskToWidth(value, bit_width));
          }
        }
      }
      if (maybe_false) {
        IntSet false_values;
        if (evalConcreteIntegers(SI->getFalseValue(), ctx, memo,
                                 in_progress, depth + 1, false_values)) {
          for (uint64_t value : false_values) {
            PushUnique(values, maskToWidth(value, bit_width));
          }
        }
      }
    }
  } else if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    IntSet lhs_values;
    IntSet rhs_values;
    if (evalConcreteIntegers(BO->getOperand(0), ctx, memo,
                             in_progress, depth + 1, lhs_values) &&
        evalConcreteIntegers(BO->getOperand(1), ctx, memo,
                             in_progress, depth + 1, rhs_values)) {
      for (uint64_t lhs : lhs_values) {
        for (uint64_t rhs : rhs_values) {
          uint64_t result = 0;
          switch (BO->getOpcode()) {
            case llvm::Instruction::Add:
              result = lhs + rhs;
              break;
            case llvm::Instruction::Sub:
              result = lhs - rhs;
              break;
            case llvm::Instruction::Mul:
              result = lhs * rhs;
              break;
            case llvm::Instruction::And:
              result = lhs & rhs;
              break;
            case llvm::Instruction::Or:
              result = lhs | rhs;
              break;
            case llvm::Instruction::Xor:
              result = lhs ^ rhs;
              break;
            case llvm::Instruction::Shl:
              result = lhs << (rhs & 63U);
              break;
            case llvm::Instruction::LShr:
              result = lhs >> (rhs & 63U);
              break;
            case llvm::Instruction::AShr:
              result = signExtendTo64(lhs, bit_width) >> (rhs & 63U);
              break;
            default:
              continue;
          }
          PushUnique(values, maskToWidth(result, bit_width));
          if (values.size() >= kMaxSolvedValues) {
            break;
          }
        }
        if (values.size() >= kMaxSolvedValues) {
          break;
        }
      }
    }
  } else if (auto *Cmp = llvm::dyn_cast<llvm::ICmpInst>(V)) {
    IntSet lhs_values;
    IntSet rhs_values;
    if (evalConcreteIntegers(Cmp->getOperand(0), ctx, memo,
                             in_progress, depth + 1, lhs_values) &&
        evalConcreteIntegers(Cmp->getOperand(1), ctx, memo,
                             in_progress, depth + 1, rhs_values)) {
      for (uint64_t lhs : lhs_values) {
        for (uint64_t rhs : rhs_values) {
          bool result = false;
          switch (Cmp->getPredicate()) {
            case llvm::CmpInst::ICMP_EQ:
              result = lhs == rhs;
              break;
            case llvm::CmpInst::ICMP_NE:
              result = lhs != rhs;
              break;
            case llvm::CmpInst::ICMP_UGT:
              result = lhs > rhs;
              break;
            case llvm::CmpInst::ICMP_UGE:
              result = lhs >= rhs;
              break;
            case llvm::CmpInst::ICMP_ULT:
              result = lhs < rhs;
              break;
            case llvm::CmpInst::ICMP_ULE:
              result = lhs <= rhs;
              break;
            case llvm::CmpInst::ICMP_SGT:
              result = static_cast<int64_t>(signExtendTo64(lhs, bit_width)) >
                       static_cast<int64_t>(signExtendTo64(rhs, bit_width));
              break;
            case llvm::CmpInst::ICMP_SGE:
              result = static_cast<int64_t>(signExtendTo64(lhs, bit_width)) >=
                       static_cast<int64_t>(signExtendTo64(rhs, bit_width));
              break;
            case llvm::CmpInst::ICMP_SLT:
              result = static_cast<int64_t>(signExtendTo64(lhs, bit_width)) <
                       static_cast<int64_t>(signExtendTo64(rhs, bit_width));
              break;
            case llvm::CmpInst::ICMP_SLE:
              result = static_cast<int64_t>(signExtendTo64(lhs, bit_width)) <=
                       static_cast<int64_t>(signExtendTo64(rhs, bit_width));
              break;
            default:
              continue;
          }
          PushUnique(values, result ? 1ULL : 0ULL);
        }
      }
    }
  } else if (auto *Cast = llvm::dyn_cast<llvm::CastInst>(V)) {
    IntSet src_values;
    if (evalConcreteIntegers(Cast->getOperand(0), ctx, memo,
                             in_progress, depth + 1, src_values)) {
      const unsigned src_width =
          Cast->getSrcTy()->isIntegerTy()
              ? Cast->getSrcTy()->getIntegerBitWidth()
              : 64;
      for (uint64_t value : src_values) {
        uint64_t out_value = value;
        if (llvm::isa<llvm::TruncInst>(Cast)) {
          out_value = maskToWidth(value, bit_width);
        } else if (llvm::isa<llvm::ZExtInst>(Cast)) {
          out_value = maskToWidth(value, src_width);
        } else if (llvm::isa<llvm::SExtInst>(Cast)) {
          out_value = signExtendTo64(value, src_width);
        } else if (llvm::isa<llvm::BitCastInst>(Cast)) {
          out_value = value;
        } else {
          continue;
        }
        PushUnique(values, maskToWidth(out_value, bit_width));
      }
    }
  } else if (auto *Freeze = llvm::dyn_cast<llvm::FreezeInst>(V)) {
    IntSet src_values;
    if (evalConcreteIntegers(Freeze->getOperand(0), ctx, memo,
                             in_progress, depth + 1, src_values)) {
      for (uint64_t value : src_values) {
        PushUnique(values, maskToWidth(value, bit_width));
      }
    }
  }

  in_progress.erase(V);
  memo[V] = values;
  out = values;
  return !out.empty();
}

static SolvedIntegerValue solveIntegerValue(llvm::Value *V,
                                            SolverEvalContext &ctx) {
  SolvedIntegerValue solved;
  if (!V) {
    return solved;
  }

  solved.bit_width =
      V->getType()->isIntegerTy() ? V->getType()->getIntegerBitWidth() : 64;

  llvm::DenseMap<llvm::Value *, IntSet> memo;
  llvm::SmallPtrSet<llvm::Value *, 32> in_progress;
  IntSet values;
  if (!evalConcreteIntegers(V, ctx, memo, in_progress, 0, values)) {
    return solved;
  }

  for (uint64_t value : values) {
    PushUnique(solved.values, maskToWidth(value, solved.bit_width));
  }
  if (solved.values.empty()) {
    return solved;
  }
  solved.kind = solved.values.size() == 1 ? SolvedIntegerValueKind::kConstant
                                          : SolvedIntegerValueKind::kSet;
  return solved;
}

struct OptimizedFunctionView {
  std::unique_ptr<llvm::Module> module;
  std::unique_ptr<llvm::LoopAnalysisManager> lam;
  std::unique_ptr<llvm::FunctionAnalysisManager> fam;
  std::unique_ptr<llvm::CGSCCAnalysisManager> cgam;
  std::unique_ptr<llvm::ModuleAnalysisManager> mam;
  llvm::Function *function = nullptr;
};

static OptimizedFunctionView buildOptimizedView(llvm::Function &F) {
  OptimizedFunctionView view;
  view.module = llvm::CloneModule(*F.getParent());
  if (!view.module) {
    return view;
  }
  view.function = view.module->getFunction(F.getName());
  if (!view.function) {
    view.module.reset();
    return view;
  }

  view.lam = std::make_unique<llvm::LoopAnalysisManager>();
  view.fam = std::make_unique<llvm::FunctionAnalysisManager>();
  view.cgam = std::make_unique<llvm::CGSCCAnalysisManager>();
  view.mam = std::make_unique<llvm::ModuleAnalysisManager>();
  llvm::PassBuilder PB;
  PB.registerFunctionAnalyses(*view.fam);
  PB.registerModuleAnalyses(*view.mam);
  PB.registerCGSCCAnalyses(*view.cgam);
  PB.registerLoopAnalyses(*view.lam);
  PB.crossRegisterProxies(*view.lam, *view.fam, *view.cgam, *view.mam);

  llvm::FunctionPassManager FPM;
  buildStateOptimizationPipeline(FPM, false);
  FPM.addPass(llvm::SROAPass(llvm::SROAOptions::ModifyCFG));
  FPM.addPass(llvm::EarlyCSEPass());
  FPM.addPass(llvm::InstCombinePass());
  FPM.addPass(llvm::GVNPass());
  FPM.addPass(llvm::SCCPPass());
  FPM.addPass(llvm::SimplifyCFGPass());
  FPM.run(*view.function, *view.fam);
  return view;
}

static std::optional<SolvedIntegerValue> solveFieldBeforeSiteInFunction(
    llvm::Function &F, uint64_t control_pc, llvm::StringRef field_name,
    llvm::MemorySSA *memory_ssa = nullptr) {
  auto site = findControlTransferSite(F, control_pc);
  if (!site.inst) {
    return std::nullopt;
  }

  SolverEvalContext ctx(F);
  ctx.memory_ssa = memory_ssa;
  auto field = ctx.field_map.fieldByName(field_name.upper());
  if (!field) {
    return std::nullopt;
  }

  llvm::DominatorTree DT(F);
  SolvedIntegerValue merged;
  merged.bit_width = field->size * 8U;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *store = llvm::dyn_cast<llvm::StoreInst>(&I);
      if (!store || !DT.dominates(store, site.inst)) {
        continue;
      }
      auto resolved = ctx.field_map.resolvePointer(store->getPointerOperand());
      if (!resolved || resolved->offset != field->offset) {
        continue;
      }
      auto value = solveIntegerValue(store->getValueOperand(), ctx);
      if (value.kind == SolvedIntegerValueKind::kUnknown) {
        continue;
      }
      for (uint64_t element : value.values) {
        PushUnique(merged.values, maskToWidth(element, merged.bit_width));
      }
      if (merged.values.size() >= kMaxSolvedValues) {
        break;
      }
    }
    if (merged.values.size() >= kMaxSolvedValues) {
      break;
    }
  }

  if (merged.values.empty() && ctx.memory_ssa) {
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *load = llvm::dyn_cast<llvm::LoadInst>(&I);
        if (!load || !DT.dominates(load, site.inst))
          continue;
        auto resolved = ctx.field_map.resolvePointer(load->getPointerOperand());
        if (!resolved || resolved->offset != field->offset)
          continue;
        auto value = solveIntegerValue(load, ctx);
        if (value.kind == SolvedIntegerValueKind::kUnknown)
          continue;
        for (uint64_t element : value.values) {
          PushUnique(merged.values, maskToWidth(element, merged.bit_width));
        }
        if (merged.values.size() >= kMaxSolvedValues)
          break;
      }
      if (merged.values.size() >= kMaxSolvedValues)
        break;
    }
  }

  if (merged.values.empty()) {
    return std::nullopt;
  }
  merged.kind = merged.values.size() == 1 ? SolvedIntegerValueKind::kConstant
                                          : SolvedIntegerValueKind::kSet;
  return merged;
}

static void collectStateFlagsForSolution(llvm::Function &F, uint64_t control_pc,
                                         RemillControlTransferSolution &solution) {
  static constexpr const char *kFlags[] = {
      "CF", "PF", "AF", "ZF", "SF", "OF", "DF",
  };
  for (auto *flag : kFlags) {
    if (auto solved = solveFieldBeforeSiteInFunction(F, control_pc, flag)) {
      solution.named_state_values[flag] = *solved;
    }
  }
}

}  // namespace

std::optional<uint64_t> SolvedIntegerValue::constant() const {
  if (kind == SolvedIntegerValueKind::kConstant && values.size() == 1) {
    return values.front();
  }
  return std::nullopt;
}

std::optional<bool> SolvedIntegerValue::constantBool() const {
  auto c = constant();
  if (!c) {
    return std::nullopt;
  }
  return *c != 0;
}

RemillStateVariableSolver::RemillStateVariableSolver(llvm::Module &M)
    : module_(M) {}

std::optional<RemillControlTransferSolution>
RemillStateVariableSolver::solveControlTransfer(llvm::Function &F,
                                                uint64_t control_pc) {
  auto view = buildOptimizedView(F);
  if (!view.function) {
    return std::nullopt;
  }

  auto site = findControlTransferSite(*view.function, control_pc);
  if (!site.inst) {
    return std::nullopt;
  }
  SolverEvalContext ctx(*view.function);
  if (view.fam) {
    auto &memory_ssa_result =
        view.fam->getResult<llvm::MemorySSAAnalysis>(*view.function);
    ctx.memory_ssa = &memory_ssa_result.getMSSA();
  }

  RemillControlTransferSolution solution;
  solution.control_pc = control_pc;

  if (site.kind == SolverSite::Kind::kConditionalBranch) {
    auto *branch = llvm::cast<llvm::BranchInst>(site.inst);
    solution.kind = RemillControlTransferKind::kConditionalBranch;
    solution.transfer_value = solveIntegerValue(branch->getCondition(), ctx);
    solution.branch_taken = solution.transfer_value.constantBool();
    const auto taken_target =
        extractTransferTargetFromBlock(branch->getSuccessor(0));
    const auto not_taken_target =
        extractTransferTargetFromBlock(branch->getSuccessor(1));
    if (solution.branch_taken.has_value()) {
      const auto selected_target =
          *solution.branch_taken ? taken_target : not_taken_target;
      if (selected_target) {
        solution.possible_target_pcs.push_back(*selected_target);
      }
    } else {
      if (taken_target) {
        PushUnique(solution.possible_target_pcs, *taken_target);
      }
      if (not_taken_target) {
        PushUnique(solution.possible_target_pcs, *not_taken_target);
      }
    }
    collectStateFlagsForSolution(*view.function, control_pc, solution);
    return solution;
  }

  auto *call = llvm::dyn_cast<llvm::CallBase>(site.inst);
  if (!call || call->arg_size() < 2) {
    return std::nullopt;
  }

  solution.kind = site.kind == SolverSite::Kind::kDispatchJump
                      ? RemillControlTransferKind::kIndirectJump
                      : RemillControlTransferKind::kIndirectCall;
  solution.transfer_value = solveIntegerValue(call->getArgOperand(1), ctx);
  for (uint64_t target : solution.transfer_value.values) {
    if (target != 0) {
      PushUnique(solution.possible_target_pcs, target);
    }
  }
  collectStateFlagsForSolution(*view.function, control_pc, solution);
  return solution;
}

std::optional<SolvedIntegerValue>
RemillStateVariableSolver::solveStateFieldBeforeControlTransfer(
    llvm::Function &F, uint64_t control_pc, llvm::StringRef field_name) {
  if (auto solved =
          solveFieldBeforeSiteInFunction(F, control_pc, field_name)) {
    return solved;
  }

  auto view = buildOptimizedView(F);
  if (!view.function) {
    return std::nullopt;
  }
  llvm::MemorySSA *memory_ssa = nullptr;
  if (view.fam) {
    auto &memory_ssa_result =
        view.fam->getResult<llvm::MemorySSAAnalysis>(*view.function);
    memory_ssa = &memory_ssa_result.getMSSA();
  }
  return solveFieldBeforeSiteInFunction(*view.function, control_pc, field_name,
                                        memory_ssa);
}

bool RemillStateVariableSolver::annotateSolvedControlTransfer(
    llvm::Function &F, uint64_t control_pc,
    RemillControlTransferSolution *solution_out) {
  auto maybe_solution = solveControlTransfer(F, control_pc);
  if (!maybe_solution) {
    return false;
  }
  if (solution_out) {
    *solution_out = *maybe_solution;
  }

  auto site = findControlTransferSite(F, control_pc);
  if (!site.inst) {
    return false;
  }

  bool changed = false;
  if (auto *call = llvm::dyn_cast<llvm::CallBase>(site.inst)) {
    llvm::SmallVector<uint64_t, 8> normalized_targets(
        maybe_solution->possible_target_pcs.begin(),
        maybe_solution->possible_target_pcs.end());
    std::sort(normalized_targets.begin(), normalized_targets.end());
    normalized_targets.erase(
        std::unique(normalized_targets.begin(), normalized_targets.end()),
        normalized_targets.end());
    const auto maybe_existing = readSolvedTargetSet(*call);
    const bool same_targets =
        maybe_existing && maybe_existing->size() == normalized_targets.size() &&
        std::equal(maybe_existing->begin(), maybe_existing->end(),
                   normalized_targets.begin());
    if (!same_targets) {
      writeSolvedTargetSet(*call, normalized_targets);
      changed = true;
    }

    if (normalized_targets.size() == 1) {
      ExecutableTargetFact fact;
      fact.raw_target_pc = normalized_targets.front();
      fact.effective_target_pc = normalized_targets.front();
      fact.kind = ExecutableTargetKind::kExecutablePlaceholder;
      fact.trust = ExecutableTargetTrust::kUntrustedExecutable;
      writeExecutableTargetFact(*call, fact);
      changed = true;
    }
  } else if (auto *branch = llvm::dyn_cast<llvm::BranchInst>(site.inst);
             branch && maybe_solution->branch_taken.has_value()) {
    if (readSolvedBranchTaken(*branch) != maybe_solution->branch_taken) {
      writeSolvedBranchTaken(*branch, *maybe_solution->branch_taken);
      changed = true;
    }
  }

  return changed;
}

std::optional<llvm::SmallVector<uint64_t, 8>> readSolvedTargetSet(
    const llvm::CallBase &call) {
  auto *tuple = llvm::dyn_cast_or_null<llvm::MDTuple>(
      call.getMetadata(kSolvedTargetSetMetadata));
  if (!tuple || tuple->getNumOperands() == 0) {
    return std::nullopt;
  }

  llvm::SmallVector<uint64_t, 8> targets;
  for (unsigned i = 0; i < tuple->getNumOperands(); ++i) {
    auto *value =
        llvm::mdconst::dyn_extract<llvm::ConstantInt>(tuple->getOperand(i));
    if (!value) {
      continue;
    }
    PushUnique(targets, value->getZExtValue());
  }
  if (targets.empty()) {
    return std::nullopt;
  }
  return targets;
}

void writeSolvedTargetSet(llvm::CallBase &call,
                          llvm::ArrayRef<uint64_t> targets) {
  auto &ctx = call.getContext();
  if (targets.empty()) {
    call.setMetadata(kSolvedTargetSetMetadata, nullptr);
    return;
  }

  llvm::SmallVector<uint64_t, 8> unique_targets;
  for (uint64_t target : targets) {
    PushUnique(unique_targets, target);
  }
  std::sort(unique_targets.begin(), unique_targets.end());

  llvm::SmallVector<llvm::Metadata *, 8> ops;
  ops.reserve(unique_targets.size());
  for (uint64_t target : unique_targets) {
    ops.push_back(llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(llvm::Type::getInt64Ty(ctx), target)));
  }
  call.setMetadata(kSolvedTargetSetMetadata, llvm::MDTuple::get(ctx, ops));
}

std::optional<bool> readSolvedBranchTaken(const llvm::Instruction &inst) {
  auto *tuple = llvm::dyn_cast_or_null<llvm::MDTuple>(
      inst.getMetadata(kSolvedBranchTakenMetadata));
  if (!tuple || tuple->getNumOperands() == 0) {
    return std::nullopt;
  }
  auto *value =
      llvm::mdconst::dyn_extract<llvm::ConstantInt>(tuple->getOperand(0));
  if (!value) {
    return std::nullopt;
  }
  return value->getZExtValue() != 0;
}

void writeSolvedBranchTaken(llvm::Instruction &inst, bool taken) {
  auto &ctx = inst.getContext();
  inst.setMetadata(
      kSolvedBranchTakenMetadata,
      llvm::MDTuple::get(
          ctx, {llvm::ConstantAsMetadata::get(llvm::ConstantInt::get(
                    llvm::Type::getInt1Ty(ctx), taken ? 1 : 0))}));
}

}  // namespace omill
