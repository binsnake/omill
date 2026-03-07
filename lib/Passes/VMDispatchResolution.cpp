#include "omill/Passes/VMDispatchResolution.h"

#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>
#include <llvm/Support/raw_ostream.h>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VMHandlerGraph.h"

namespace omill {

namespace {

/// Extract a handler VA from a function name like "sub_1402A1000".
static std::optional<uint64_t> extractVAFromName(llvm::StringRef name) {
  if (!name.starts_with("sub_"))
    return std::nullopt;
  uint64_t va = 0;
  if (name.drop_front(4).getAsInteger(16, va))
    return std::nullopt;
  return va;
}

/// Collect all calls to __omill_dispatch_jump or __omill_dispatch_call
/// in a function.
static void collectDispatchCalls(
    llvm::Function &F,
    llvm::SmallVectorImpl<llvm::CallInst *> &dispatch_jumps,
    llvm::SmallVectorImpl<llvm::CallInst *> &dispatch_calls) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallInst>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || call->arg_size() < 3)
        continue;

      auto name = callee->getName();
      if (name == "__omill_dispatch_jump")
        dispatch_jumps.push_back(call);
      else if (name == "__omill_dispatch_call")
        dispatch_calls.push_back(call);
    }
  }
}

/// Check if a constant looks like it could be an RVA (relative to image base).
/// RVAs for EAC handlers are typically in the range 0x20000..0x3FFFFFFF.
static bool isPlausibleRVA(uint64_t val) {
  return val >= 0x1000 && val <= 0x7FFFFFFF;
}

static uint64_t getImageBase(const VMHandlerGraph &graph,
                             const BinaryMemoryMap &memory) {
  if (graph.imageBase() != 0)
    return graph.imageBase();
  return memory.imageBase();
}

static std::optional<uint64_t> resolvePlausibleRVA(uint64_t val,
                                                   const VMHandlerGraph &graph,
                                                   const BinaryMemoryMap &memory) {
  if (!isPlausibleRVA(val))
    return std::nullopt;
  if (auto resolved = graph.resolveRVA(static_cast<uint32_t>(val)))
    return *resolved;

  uint64_t image_base = getImageBase(graph, memory);
  if (image_base != 0)
    return image_base + val;
  return std::nullopt;
}

static llvm::Value *forwardLoadInBlock(llvm::LoadInst *load) {
  auto *block = load->getParent();
  for (auto it = load->getIterator(); it != block->begin();) {
    --it;
    if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&*it)) {
      if (store->getPointerOperand() == load->getPointerOperand())
        return store->getValueOperand();
      continue;
    }
    if (llvm::isa<llvm::CallBase>(&*it))
      return nullptr;
  }
  return nullptr;
}

static std::optional<uint64_t> readLoadFromBinaryMemory(llvm::LoadInst *load,
                                                        const BinaryMemoryMap &memory,
                                                        uint64_t addr) {
  unsigned byte_size = 0;
  if (load->getType()->isPointerTy()) {
    byte_size = 8;
  } else if (load->getType()->isIntegerTy()) {
    byte_size = load->getType()->getIntegerBitWidth() / 8;
  } else {
    return std::nullopt;
  }

  if (byte_size == 0 || byte_size > 8)
    return std::nullopt;
  return memory.readInt(addr, byte_size);
}

/// Recursively try to resolve a dispatch target value to a constant VA.
///
/// Handles these patterns:
///   1. ConstantInt: already a constant VA
///   2. add i64 %X, <const>: image_base + RVA
///   3. add i64 %X, %Y: recursively check if one operand resolves
///   4. select i1 %cond, %a, %b: resolve both branches (returns nullopt,
///      but populates resolved_select if both branches resolve)
///
/// Returns the resolved constant VA, or nullopt if unresolvable.
///
/// \param depth  Recursion depth limit.
static std::optional<uint64_t>
resolveTargetValue(llvm::Value *V, const VMHandlerGraph &graph,
                   const BinaryMemoryMap &memory, uint64_t handler_va,
                   llvm::SmallPtrSetImpl<llvm::Value *> &visiting,
                   unsigned depth = 0) {
  if (depth > 24)
    return std::nullopt;
  if (!visiting.insert(V).second)
    return std::nullopt;
  auto erase_visit = llvm::make_scope_exit([&] { visiting.erase(V); });

  // Already a constant.
  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(V))
    return ci->getZExtValue();

  if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(V)) {
    switch (ce->getOpcode()) {
    case llvm::Instruction::IntToPtr:
    case llvm::Instruction::PtrToInt:
    case llvm::Instruction::BitCast:
      return resolveTargetValue(ce->getOperand(0), graph, memory, handler_va,
                                visiting, depth + 1);
    default:
      return std::nullopt;
    }
  }

  auto *inst = llvm::dyn_cast<llvm::Instruction>(V);
  if (!inst)
    return std::nullopt;

  // Pattern: %program_counter argument (arg1 of lifted function).
  // In remill-lifted functions, arg1 is the initial program counter = handler VA.
  if (auto *arg = llvm::dyn_cast<llvm::Argument>(V)) {
    if (arg->getArgNo() == 1)
      return handler_va;
  }

  // Pattern: zext/sext/trunc/bitcasts on integer dispatch values.
  if (auto *zext = llvm::dyn_cast<llvm::ZExtInst>(inst))
    return resolveTargetValue(zext->getOperand(0), graph, memory, handler_va,
                              visiting, depth + 1);
  if (auto *sext = llvm::dyn_cast<llvm::SExtInst>(inst)) {
    auto inner = resolveTargetValue(sext->getOperand(0), graph, memory,
                                    handler_va, visiting, depth + 1);
    if (!inner)
      return std::nullopt;
    unsigned src_bits = sext->getOperand(0)->getType()->getIntegerBitWidth();
    if (src_bits == 0 || src_bits >= 64)
      return *inner;
    uint64_t value = *inner;
    if (value & (1ULL << (src_bits - 1)))
      value |= ~((1ULL << src_bits) - 1);
    return value;
  }

  // Pattern: trunc i64 %X to i32 (RVA truncation)
  if (auto *trunc = llvm::dyn_cast<llvm::TruncInst>(inst)) {
    auto inner = resolveTargetValue(trunc->getOperand(0), graph, memory,
                                    handler_va, visiting, depth + 1);
    if (!inner)
      return std::nullopt;
    unsigned dst_bits = trunc->getType()->getIntegerBitWidth();
    if (dst_bits == 0 || dst_bits >= 64)
      return *inner;
    return *inner & ((1ULL << dst_bits) - 1);
  }

  if (auto *ptr_to_int = llvm::dyn_cast<llvm::PtrToIntInst>(inst))
    return resolveTargetValue(ptr_to_int->getOperand(0), graph, memory,
                              handler_va, visiting, depth + 1);
  if (auto *int_to_ptr = llvm::dyn_cast<llvm::IntToPtrInst>(inst))
    return resolveTargetValue(int_to_ptr->getOperand(0), graph, memory,
                              handler_va, visiting, depth + 1);
  if (auto *bitcast = llvm::dyn_cast<llvm::BitCastInst>(inst))
    return resolveTargetValue(bitcast->getOperand(0), graph, memory,
                              handler_va, visiting, depth + 1);
  if (auto *freeze = llvm::dyn_cast<llvm::FreezeInst>(inst))
    return resolveTargetValue(freeze->getOperand(0), graph, memory,
                              handler_va, visiting, depth + 1);

  if (auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(inst)) {
    auto lhs = resolveTargetValue(icmp->getOperand(0), graph, memory,
                                  handler_va, visiting, depth + 1);
    auto rhs = resolveTargetValue(icmp->getOperand(1), graph, memory,
                                  handler_va, visiting, depth + 1);
    if (!lhs || !rhs)
      return std::nullopt;

    bool result = false;
    switch (icmp->getPredicate()) {
    case llvm::CmpInst::ICMP_EQ:
      result = (*lhs == *rhs);
      break;
    case llvm::CmpInst::ICMP_NE:
      result = (*lhs != *rhs);
      break;
    case llvm::CmpInst::ICMP_UGT:
      result = (*lhs > *rhs);
      break;
    case llvm::CmpInst::ICMP_UGE:
      result = (*lhs >= *rhs);
      break;
    case llvm::CmpInst::ICMP_ULT:
      result = (*lhs < *rhs);
      break;
    case llvm::CmpInst::ICMP_ULE:
      result = (*lhs <= *rhs);
      break;
    case llvm::CmpInst::ICMP_SGT:
      result = (static_cast<int64_t>(*lhs) > static_cast<int64_t>(*rhs));
      break;
    case llvm::CmpInst::ICMP_SGE:
      result = (static_cast<int64_t>(*lhs) >= static_cast<int64_t>(*rhs));
      break;
    case llvm::CmpInst::ICMP_SLT:
      result = (static_cast<int64_t>(*lhs) < static_cast<int64_t>(*rhs));
      break;
    case llvm::CmpInst::ICMP_SLE:
      result = (static_cast<int64_t>(*lhs) <= static_cast<int64_t>(*rhs));
      break;
    default:
      return std::nullopt;
    }
    return result ? 1ULL : 0ULL;
  }

  if (auto *select = llvm::dyn_cast<llvm::SelectInst>(inst)) {
    auto cond = resolveTargetValue(select->getCondition(), graph, memory,
                                   handler_va, visiting, depth + 1);
    if (cond) {
      llvm::Value *chosen = (*cond != 0) ? select->getTrueValue()
                                         : select->getFalseValue();
      return resolveTargetValue(chosen, graph, memory, handler_va, visiting,
                                depth + 1);
    }

    auto true_value = resolveTargetValue(select->getTrueValue(), graph, memory,
                                         handler_va, visiting, depth + 1);
    auto false_value =
        resolveTargetValue(select->getFalseValue(), graph, memory, handler_va,
                           visiting, depth + 1);
    if (true_value && false_value && *true_value == *false_value)
      return *true_value;
    return std::nullopt;
  }

  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(inst)) {
    if (phi->getNumIncomingValues() == 0)
      return std::nullopt;

    std::optional<uint64_t> agreed;
    for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
      auto incoming =
          resolveTargetValue(phi->getIncomingValue(i), graph, memory,
                             handler_va, visiting, depth + 1);
      if (!incoming)
        return std::nullopt;
      if (!agreed)
        agreed = incoming;
      else if (*agreed != *incoming)
        return std::nullopt;
    }
    return agreed;
  }

  if (auto *load = llvm::dyn_cast<llvm::LoadInst>(inst)) {
    llvm::Value *pointer = load->getPointerOperand()->stripPointerCasts();
    llvm::Value *address_expr = nullptr;
    if (auto *int_to_ptr = llvm::dyn_cast<llvm::IntToPtrInst>(pointer)) {
      address_expr = int_to_ptr->getOperand(0);
    } else if (auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(pointer)) {
      if (ce->getOpcode() == llvm::Instruction::IntToPtr)
        address_expr = ce->getOperand(0);
    }

    if (address_expr) {
      auto address = resolveTargetValue(address_expr, graph, memory, handler_va,
                                        visiting, depth + 1);
      if (address) {
        if (auto value = readLoadFromBinaryMemory(load, memory, *address))
          return value;
      }
    }

    if (auto *forwarded = forwardLoadInBlock(load))
      return resolveTargetValue(forwarded, graph, memory, handler_va, visiting,
                                depth + 1);

    return std::nullopt;
  }

  if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(inst)) {
    auto lhs = resolveTargetValue(bin->getOperand(0), graph, memory,
                                  handler_va, visiting, depth + 1);
    auto rhs = resolveTargetValue(bin->getOperand(1), graph, memory,
                                  handler_va, visiting, depth + 1);

    switch (bin->getOpcode()) {
    case llvm::Instruction::Add:
      if (lhs && rhs)
        return *lhs + *rhs;
      if (lhs) {
        if (auto rva_target = resolvePlausibleRVA(*lhs, graph, memory))
          return rva_target;
      }
      if (rhs) {
        if (auto rva_target = resolvePlausibleRVA(*rhs, graph, memory))
          return rva_target;
      }
      return std::nullopt;
    case llvm::Instruction::Sub:
      if (lhs && rhs)
        return *lhs - *rhs;
      return std::nullopt;
    case llvm::Instruction::Mul:
      if (lhs && rhs)
        return *lhs * *rhs;
      return std::nullopt;
    case llvm::Instruction::Xor:
      if (lhs && rhs)
        return *lhs ^ *rhs;
      return std::nullopt;
    case llvm::Instruction::Or:
      if (lhs && rhs)
        return *lhs | *rhs;
      return std::nullopt;
    case llvm::Instruction::And:
      if (lhs && rhs)
        return *lhs & *rhs;
      return std::nullopt;
    case llvm::Instruction::Shl:
      if (lhs && rhs)
        return (*rhs < 64) ? (*lhs << *rhs) : 0ULL;
      return std::nullopt;
    case llvm::Instruction::LShr:
      if (lhs && rhs)
        return (*rhs < 64) ? (*lhs >> *rhs) : 0ULL;
      return std::nullopt;
    case llvm::Instruction::AShr:
      if (!lhs || !rhs)
        return std::nullopt;
      if (*rhs >= 64)
        return (*lhs & (1ULL << 63)) ? ~0ULL : 0ULL;
      return static_cast<uint64_t>(
          static_cast<int64_t>(*lhs) >> static_cast<int64_t>(*rhs));
    default:
      return std::nullopt;
    }
  }

  return std::nullopt;
}

/// Try to resolve a select instruction's dispatch target.
/// Returns true if the select was replaced with a new select of constants.
static bool resolveSelectTarget(llvm::CallInst *call, llvm::SelectInst *sel,
                                const VMHandlerGraph &graph,
                                const BinaryMemoryMap &memory,
                                llvm::Module &M, uint64_t handler_va) {
  llvm::SmallPtrSet<llvm::Value *, 16> true_visiting;
  auto resolved_true =
      resolveTargetValue(sel->getTrueValue(), graph, memory, handler_va,
                         true_visiting);
  llvm::SmallPtrSet<llvm::Value *, 16> false_visiting;
  auto resolved_false =
      resolveTargetValue(sel->getFalseValue(), graph, memory, handler_va,
                         false_visiting);

  if (!resolved_true || !resolved_false)
    return false;

  auto &ctx = M.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *const_true = llvm::ConstantInt::get(i64_ty, *resolved_true);
  auto *const_false = llvm::ConstantInt::get(i64_ty, *resolved_false);

  // Build: select %cond, const_true, const_false
  llvm::IRBuilder<> builder(call);
  auto *new_sel =
      builder.CreateSelect(sel->getCondition(), const_true, const_false);
  call->setArgOperand(1, new_sel);
  return true;
}

}  // namespace

llvm::PreservedAnalyses VMDispatchResolutionPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &graph = MAM.getResult<VMHandlerGraphAnalysis>(M);
  auto &memory = MAM.getResult<BinaryMemoryAnalysis>(M);
  if (graph.empty() && memory.empty())
    return llvm::PreservedAnalyses::all();

  unsigned resolved_count = 0;
  unsigned select_count = 0;
  unsigned skipped_count = 0;
  unsigned discovery_count = 0;
  auto &ctx = M.getContext();
  auto *i64_ty = llvm::Type::getInt64Ty(ctx);

  // Collect newly-discovered target VAs (image_base + RVA for VAs not yet
  // in the module as function definitions).
  llvm::DenseSet<uint64_t> discovered_targets;

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.hasFnAttribute("omill.vm_handler"))
      continue;

    auto va_opt = extractVAFromName(F.getName());
    if (!va_opt)
      continue;
    uint64_t handler_va = *va_opt;

    // Collect dispatch calls in this function.
    llvm::SmallVector<llvm::CallInst *, 4> dispatch_jumps, dispatch_calls;
    collectDispatchCalls(F, dispatch_jumps, dispatch_calls);

    auto resolve_calls = [&](llvm::SmallVectorImpl<llvm::CallInst *> &calls) {
      for (auto *call : calls) {
        auto *target_val = call->getArgOperand(1);

        // Skip already-resolved (constant) targets.
        if (llvm::isa<llvm::ConstantInt>(target_val))
          continue;

        // Priority 1: chain-solved targets from VMHandlerChainSolver.
        // The chain solver concretely emulates handlers and knows the exact
        // successor VA.  This takes priority over IR pattern matching because
        // the IR-level `image_base + RVA` formula is wrong for EAC-style VMs
        // where the dispatch base is `delta` (not image_base).
        {
          auto chain_succs = graph.getChainTargets(handler_va);
          if (chain_succs.size() == 1) {
            auto *const_target =
                llvm::ConstantInt::get(i64_ty, chain_succs[0]);
            call->setArgOperand(1, const_target);
            ++resolved_count;

            std::string target_name =
                "sub_" + llvm::Twine::utohexstr(chain_succs[0]).str();
            if (!M.getFunction(target_name))
              discovered_targets.insert(chain_succs[0]);
            continue;
          }
          if (chain_succs.size() == 2) {
            // Two successors — can't determine which branch without
            // analyzing the condition. For now, skip.
            // TODO: match the IR-level branch condition to pick the right
            // successor, or emit a select of both.
          }
        }

        // Priority 2: recursive IR pattern resolution.
        llvm::SmallPtrSet<llvm::Value *, 16> visiting;
        if (auto resolved =
                resolveTargetValue(target_val, graph, memory, handler_va,
                                   visiting)) {
          auto *const_target = llvm::ConstantInt::get(i64_ty, *resolved);
          call->setArgOperand(1, const_target);
          ++resolved_count;

          std::string target_name =
              "sub_" + llvm::Twine::utohexstr(*resolved).str();
          if (!M.getFunction(target_name)) {
            discovered_targets.insert(*resolved);
          }
          continue;
        }

        // Priority 3: select-specific resolution.
        if (auto *sel = llvm::dyn_cast<llvm::SelectInst>(target_val)) {
          if (resolveSelectTarget(call, sel, graph, memory, M, handler_va)) {
            ++select_count;

            if (auto *new_sel =
                    llvm::dyn_cast<llvm::SelectInst>(call->getArgOperand(1))) {
              for (auto *op :
                   {new_sel->getTrueValue(), new_sel->getFalseValue()}) {
                if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(op)) {
                  std::string name =
                      "sub_" +
                      llvm::Twine::utohexstr(ci->getZExtValue()).str();
                  if (!M.getFunction(name))
                    discovered_targets.insert(ci->getZExtValue());
                }
              }
            }
            continue;
          }
        }

        ++skipped_count;
      }
    };

    // Two passes: second pass may benefit from earlier resolutions.
    // Only resolve dispatch_jumps with chain targets — these are the
    // handler-to-handler dispatch mechanism (jmp trampoline → next handler).
    // dispatch_calls within VM handlers are native function calls
    // (vmexit → call [rsp+8] → vmentry) whose targets are unrelated to
    // the handler chain succession.
    resolve_calls(dispatch_jumps);
    resolve_calls(dispatch_jumps);
  }

  // Store discovered targets as named metadata so the tool can re-lift them.
  if (!discovered_targets.empty()) {
    // Clear any previous discovered targets.
    if (auto *old_md = M.getNamedMetadata("omill.vm_discovered_targets"))
      M.eraseNamedMetadata(old_md);

    auto *named_md =
        M.getOrInsertNamedMetadata("omill.vm_discovered_targets");
    for (auto va : discovered_targets) {
      auto *ci_md = llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(i64_ty, va));
      named_md->addOperand(llvm::MDTuple::get(ctx, {ci_md}));
    }
    discovery_count = discovered_targets.size();
  }

  llvm::errs() << "VMDispatchResolution: resolved " << resolved_count;
  if (select_count > 0)
    llvm::errs() << " + " << select_count << " selects";
  if (skipped_count > 0)
    llvm::errs() << ", skipped " << skipped_count;
  if (discovery_count > 0)
    llvm::errs() << ", discovered " << discovery_count << " new targets";
  llvm::errs() << "\n";

  if (resolved_count == 0 && select_count == 0)
    return llvm::PreservedAnalyses::all();
  return llvm::PreservedAnalyses::none();
}

}  // namespace omill
