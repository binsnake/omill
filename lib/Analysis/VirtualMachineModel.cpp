#include "omill/Analysis/VirtualMachineModel.h"

#include <llvm/ADT/APInt.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/ScopeExit.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Type.h>

#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <map>
#include <set>
#include <sstream>
#include <tuple>

#include "omill/Analysis/BinaryMemoryMap.h"
#include "omill/Analysis/VMTraceEmulator.h"
#include "omill/Arch/ArchABI.h"
#include "omill/Utils/StateFieldMap.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/ProtectedBoundaryUtils.h"

namespace omill {

namespace {

static bool vmModelImportDebugEnabled() {
  const char *v = std::getenv("OMILL_DEBUG_VIRTUAL_MODEL_IMPORT");
  return v && v[0] != '\0';
}

static void vmModelImportDebugLog(llvm::StringRef message) {
  if (!vmModelImportDebugEnabled())
    return;
  llvm::errs() << "[omill.vm-model.import] " << message << "\n";
}

static bool vmModelLocalReplayDebugEnabled() {
  const char *v = std::getenv("OMILL_DEBUG_VIRTUAL_MODEL_LOCAL_REPLAY");
  return v && v[0] != '\0';
}

static void vmModelLocalReplayDebugLog(llvm::StringRef message) {
  if (!vmModelLocalReplayDebugEnabled())
    return;
  llvm::errs() << "[omill.vm-model.local-replay] " << message << "\n";
}

static std::string normalizeBoundaryName(llvm::StringRef name) {
  return name.lower();
}

static std::string syntheticBoundaryName(uint64_t entry_va) {
  return normalizeBoundaryName(std::string("vm_entry_") +
                               llvm::utohexstr(entry_va));
}

static uint64_t parseLeadingHex(llvm::StringRef text) {
  size_t hex_len = 0;
  while (hex_len < text.size() && llvm::isHexDigit(text[hex_len]))
    ++hex_len;
  if (hex_len == 0)
    return 0;

  uint64_t value = 0;
  if (text.substr(0, hex_len).getAsInteger(16, value))
    return 0;
  return value;
}

static uint64_t extractLiftedPCFromName(llvm::StringRef name) {
  if (uint64_t va = extractEntryVA(name))
    return va;

  if (name.starts_with("blk_"))
    return parseLeadingHex(name.drop_front(4));

  if (name.starts_with("block_"))
    return parseLeadingHex(name.drop_front(6));

  return 0;
}

static std::optional<uint64_t> extractHexAttr(const llvm::Function &F,
                                              llvm::StringRef attr_name) {
  auto attr = F.getFnAttribute(attr_name);
  if (!attr.isValid() || !attr.isStringAttribute())
    return std::nullopt;

  uint64_t value = 0;
  if (attr.getValueAsString().getAsInteger(16, value))
    return std::nullopt;
  return value;
}

static std::vector<VirtualSlotFact> parseSpecializationFacts(
    const llvm::Function &F) {
  auto attr = F.getFnAttribute("omill.virtual_specialization.facts");
  if (!attr.isValid() || !attr.isStringAttribute())
    return {};

  std::vector<VirtualSlotFact> facts;
  llvm::SmallVector<llvm::StringRef, 8> entries;
  attr.getValueAsString().split(entries, ',', -1, false);
  for (auto entry : entries) {
    entry = entry.trim();
    if (entry.empty())
      continue;

    auto slot_and_value = entry.split('=');
    if (slot_and_value.first.empty() || slot_and_value.second.empty())
      continue;

    auto slot_and_width = slot_and_value.first.split(':');
    unsigned slot_id = 0;
    unsigned bit_width = 0;
    uint64_t value = 0;
    if (slot_and_width.first.getAsInteger(10, slot_id))
      continue;
    if (slot_and_width.second.getAsInteger(10, bit_width))
      continue;
    if (slot_and_value.second.getAsInteger(16, value))
      continue;

    VirtualValueExpr expr;
    expr.kind = VirtualExprKind::kConstant;
    expr.bit_width = bit_width;
    expr.complete = true;
    expr.constant = value;
    facts.push_back(VirtualSlotFact{slot_id, std::move(expr)});
  }
  return facts;
}

static std::vector<VirtualStackFact> parseSpecializationStackFacts(
    const llvm::Function &F) {
  auto attr = F.getFnAttribute("omill.virtual_specialization.stack_facts");
  if (!attr.isValid() || !attr.isStringAttribute())
    return {};

  std::vector<VirtualStackFact> facts;
  llvm::SmallVector<llvm::StringRef, 8> entries;
  attr.getValueAsString().split(entries, ',', -1, false);
  for (auto entry : entries) {
    entry = entry.trim();
    if (entry.empty())
      continue;

    auto cell_and_value = entry.split('=');
    if (cell_and_value.first.empty() || cell_and_value.second.empty())
      continue;

    auto cell_and_width = cell_and_value.first.split(':');
    unsigned cell_id = 0;
    unsigned bit_width = 0;
    uint64_t value = 0;
    if (cell_and_width.first.getAsInteger(10, cell_id))
      continue;
    if (cell_and_width.second.getAsInteger(10, bit_width))
      continue;
    if (cell_and_value.second.getAsInteger(16, value))
      continue;

    VirtualValueExpr expr;
    expr.kind = VirtualExprKind::kConstant;
    expr.bit_width = bit_width;
    expr.complete = true;
    expr.constant = value;
    facts.push_back(VirtualStackFact{cell_id, std::move(expr)});
  }
  return facts;
}

static VirtualBoundaryKind classifyBoundaryKind(const llvm::Function &F) {
  auto kind_attr = F.getFnAttribute("omill.boundary_kind");
  if (kind_attr.isValid() && kind_attr.isStringAttribute()) {
    auto kind = kind_attr.getValueAsString();
    if (kind == "vm_entry_stub")
      return VirtualBoundaryKind::kProtectedEntryStub;
    return VirtualBoundaryKind::kProtectedBoundary;
  }

  if (F.hasFnAttribute("omill.protection_boundary"))
    return VirtualBoundaryKind::kProtectedBoundary;

  if (F.getName().starts_with("vm_entry_"))
    return VirtualBoundaryKind::kProtectedEntryStub;

  return VirtualBoundaryKind::kUnknown;
}

static bool isBoundaryFunction(const llvm::Function &F) {
  return classifyBoundaryKind(F) != VirtualBoundaryKind::kUnknown;
}

static bool isLiftedOrHelperSeedFunction(const llvm::Function &F) {
  if (F.isDeclaration())
    return false;
  if (F.hasFnAttribute("omill.localized_continuation_shim"))
    return false;
  auto name = F.getName();
  if (name.starts_with("sub_") || name.starts_with("blk_") ||
      name.starts_with("block_")) {
    return true;
  }
  if (F.hasFnAttribute("omill.output_root") ||
      F.hasFnAttribute("omill.virtual_specialized") ||
      F.hasFnAttribute("omill.closed_root_slice") ||
      F.hasFnAttribute("omill.vm_handler") ||
      F.hasFnAttribute("omill.vm_wrapper")) {
    return true;
  }
  return false;
}

static bool isDispatchIntrinsic(const llvm::Function &F) {
  return F.getName() == "__omill_dispatch_call" ||
         F.getName() == "__omill_dispatch_jump";
}

static bool isCallSiteHelper(const llvm::Function &F) {
  return F.getName().contains("CALLI");
}

static std::optional<unsigned> remillMemoryBitWidth(llvm::StringRef name) {
  if (name.starts_with("__remill_read_memory_"))
    name = name.drop_front(strlen("__remill_read_memory_"));
  else if (name.starts_with("__remill_write_memory_"))
    name = name.drop_front(strlen("__remill_write_memory_"));
  else
    return std::nullopt;

  unsigned bits = 0;
  if (name.getAsInteger(10, bits))
    return std::nullopt;
  return bits;
}

static bool isRemillReadMemoryIntrinsic(const llvm::Function &F) {
  return remillMemoryBitWidth(F.getName()).has_value() &&
         F.getName().starts_with("__remill_read_memory_");
}

static bool isRemillWriteMemoryIntrinsic(const llvm::Function &F) {
  return remillMemoryBitWidth(F.getName()).has_value() &&
         F.getName().starts_with("__remill_write_memory_");
}

static bool isRemillTerminalControlIntrinsic(const llvm::Function &F) {
  return F.getName() == "__remill_missing_block" ||
         F.getName() == "__remill_function_return";
}

static unsigned getValueBitWidth(llvm::Value *V, const llvm::DataLayout &dl) {
  auto *ty = V->getType();
  if (ty->isIntegerTy())
    return ty->getIntegerBitWidth();
  if (ty->isPointerTy())
    return dl.getPointerSizeInBits(ty->getPointerAddressSpace());
  return 0;
}

static std::optional<VirtualStateSlotSummary>
extractStateSlotSummary(llvm::Value *ptr, unsigned width,
                        const llvm::DataLayout &dl) {
  int64_t offset = 0;
  auto *base =
      llvm::GetPointerBaseWithConstantOffset(ptr, offset, dl, true);
  if (!base)
    return std::nullopt;

  auto *base_arg = llvm::dyn_cast<llvm::Argument>(base);
  auto *base_alloca = llvm::dyn_cast<llvm::AllocaInst>(base);
  if (!base_arg && !base_alloca)
    return std::nullopt;

  VirtualStateSlotSummary summary;
  summary.offset = offset;
  summary.width = width;
  summary.from_argument = (base_arg != nullptr);
  summary.from_alloca = (base_alloca != nullptr);

  if (base_arg) {
    summary.base_name =
        "arg" + std::to_string(static_cast<unsigned>(base_arg->getArgNo()));
  } else {
    summary.base_name = base_alloca->getName().str();
    if (summary.base_name.empty())
      summary.base_name = "alloca";
  }

  return summary;
}

static std::optional<VirtualStackCellSummary> extractStackCellSummaryFromExpr(
    const VirtualValueExpr &expr, unsigned width) {
  using BaseSummary =
      std::tuple<std::string, int64_t, unsigned, bool, bool>;
  auto expr_width_bytes = [](const VirtualValueExpr &value) {
    return value.bit_width ? std::max(1u, value.bit_width / 8u) : 8u;
  };
  auto make_summary = [&](llvm::StringRef base_name, int64_t base_offset,
                          unsigned base_width, bool base_from_argument,
                          bool base_from_alloca, int64_t cell_offset) {
    VirtualStackCellSummary summary;
    summary.base_name = base_name.str();
    summary.base_offset = base_offset;
    summary.base_width = base_width;
    summary.offset = cell_offset;
    summary.width = width;
    summary.base_from_argument = base_from_argument;
    summary.base_from_alloca = base_from_alloca;
    return summary;
  };
  auto get_base_summary =
      [&](const VirtualValueExpr &value)
          -> std::optional<std::tuple<std::string, int64_t, unsigned, bool, bool>> {
    if (value.kind == VirtualExprKind::kStateSlot &&
        value.state_base_name.has_value() && value.state_offset.has_value()) {
      auto base_name = *value.state_base_name;
      const bool from_argument = llvm::StringRef(base_name).starts_with("arg");
      return std::tuple<std::string, int64_t, unsigned, bool, bool>{
          base_name,
          *value.state_offset,
          expr_width_bytes(value),
          from_argument,
          !from_argument,
      };
    }

    if (value.kind == VirtualExprKind::kArgument &&
        value.argument_index.has_value()) {
      return std::tuple<std::string, int64_t, unsigned, bool, bool>{
          "arg" + std::to_string(*value.argument_index),
          0,
          expr_width_bytes(value),
          true,
          false,
      };
    }

    return std::nullopt;
  };

  std::function<std::optional<std::pair<BaseSummary, int64_t>>(
      const VirtualValueExpr &)>
      get_base_and_offset = [&](const VirtualValueExpr &value)
      -> std::optional<std::pair<BaseSummary, int64_t>> {
    if (auto base = get_base_summary(value))
      return std::make_pair(*base, int64_t{0});

    if ((value.kind != VirtualExprKind::kAdd &&
         value.kind != VirtualExprKind::kSub) ||
        value.operands.size() != 2) {
      return std::nullopt;
    }

    if (auto nested = get_base_and_offset(value.operands[0]);
        nested && value.operands[1].constant.has_value()) {
      int64_t delta = static_cast<int64_t>(*value.operands[1].constant);
      if (value.kind == VirtualExprKind::kSub)
        delta = -delta;
      nested->second += delta;
      return nested;
    }

    if (value.kind == VirtualExprKind::kAdd &&
        value.operands[0].constant.has_value()) {
      if (auto nested = get_base_and_offset(value.operands[1])) {
        nested->second += static_cast<int64_t>(*value.operands[0].constant);
        return nested;
      }
    }

    return std::nullopt;
  };

  if (auto flattened = get_base_and_offset(expr)) {
    const auto &[base, cell_offset] = *flattened;
    return make_summary(std::get<0>(base), std::get<1>(base),
                        std::get<2>(base), std::get<3>(base),
                        std::get<4>(base), cell_offset);
  }

  return std::nullopt;
}

static VirtualExprKind classifyExprKind(unsigned opcode) {
  switch (opcode) {
    case llvm::Instruction::Add:
      return VirtualExprKind::kAdd;
    case llvm::Instruction::Sub:
      return VirtualExprKind::kSub;
    case llvm::Instruction::Mul:
      return VirtualExprKind::kMul;
    case llvm::Instruction::Xor:
      return VirtualExprKind::kXor;
    case llvm::Instruction::And:
      return VirtualExprKind::kAnd;
    case llvm::Instruction::Or:
      return VirtualExprKind::kOr;
    case llvm::Instruction::Shl:
      return VirtualExprKind::kShl;
    case llvm::Instruction::LShr:
      return VirtualExprKind::kLShr;
    case llvm::Instruction::AShr:
      return VirtualExprKind::kAShr;
    default:
      return VirtualExprKind::kUnknown;
  }
}

static VirtualExprKind classifyICmpPredicate(llvm::CmpInst::Predicate pred) {
  switch (pred) {
    case llvm::CmpInst::ICMP_EQ:
      return VirtualExprKind::kEq;
    case llvm::CmpInst::ICMP_NE:
      return VirtualExprKind::kNe;
    case llvm::CmpInst::ICMP_ULT:
      return VirtualExprKind::kUlt;
    case llvm::CmpInst::ICMP_ULE:
      return VirtualExprKind::kUle;
    case llvm::CmpInst::ICMP_UGT:
      return VirtualExprKind::kUgt;
    case llvm::CmpInst::ICMP_UGE:
      return VirtualExprKind::kUge;
    case llvm::CmpInst::ICMP_SLT:
      return VirtualExprKind::kSlt;
    case llvm::CmpInst::ICMP_SLE:
      return VirtualExprKind::kSle;
    case llvm::CmpInst::ICMP_SGT:
      return VirtualExprKind::kSgt;
    case llvm::CmpInst::ICMP_SGE:
      return VirtualExprKind::kSge;
    default:
      return VirtualExprKind::kUnknown;
  }
}

static std::optional<uint64_t> evaluateVirtualExprImpl(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    llvm::SmallDenseSet<unsigned, 8> &visiting_slots,
    llvm::SmallDenseSet<unsigned, 8> &visiting_cells) {
  auto lookup_slot = [&](unsigned slot_id) -> std::optional<uint64_t> {
    auto it = std::find_if(facts.begin(), facts.end(),
                           [&](const VirtualSlotFact &fact) {
                             return fact.slot_id == slot_id;
                           });
    if (it == facts.end())
      return std::nullopt;
    if (!visiting_slots.insert(slot_id).second)
      return std::nullopt;
    auto value = evaluateVirtualExprImpl(it->value, facts, stack_facts,
                                         visiting_slots, visiting_cells);
    visiting_slots.erase(slot_id);
    return value;
  };

  auto lookup_stack = [&](unsigned cell_id) -> std::optional<uint64_t> {
    auto it = std::find_if(stack_facts.begin(), stack_facts.end(),
                           [&](const VirtualStackFact &fact) {
                             return fact.cell_id == cell_id;
                           });
    if (it == stack_facts.end())
      return std::nullopt;
    if (!visiting_cells.insert(cell_id).second)
      return std::nullopt;
    auto value = evaluateVirtualExprImpl(it->value, facts, stack_facts,
                                         visiting_slots, visiting_cells);
    visiting_cells.erase(cell_id);
    return value;
  };

  auto fold_binary = [&](auto fn) -> std::optional<uint64_t> {
    if (expr.operands.size() != 2)
      return std::nullopt;
    auto lhs = evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                       visiting_slots, visiting_cells);
    auto rhs = evaluateVirtualExprImpl(expr.operands[1], facts, stack_facts,
                                       visiting_slots, visiting_cells);
    if (!lhs || !rhs)
      return std::nullopt;
    return fn(*lhs, *rhs);
  };

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
      return expr.constant;
    case VirtualExprKind::kStateSlot:
      if (expr.slot_id.has_value())
        return lookup_slot(*expr.slot_id);
      return std::nullopt;
    case VirtualExprKind::kStackCell:
      if (expr.stack_cell_id.has_value())
        return lookup_stack(*expr.stack_cell_id);
      return std::nullopt;
    case VirtualExprKind::kAdd:
      return fold_binary([](uint64_t a, uint64_t b) { return a + b; });
    case VirtualExprKind::kSub:
      return fold_binary([](uint64_t a, uint64_t b) { return a - b; });
    case VirtualExprKind::kMul:
      return fold_binary([](uint64_t a, uint64_t b) { return a * b; });
    case VirtualExprKind::kXor:
      return fold_binary([](uint64_t a, uint64_t b) { return a ^ b; });
    case VirtualExprKind::kAnd:
      return fold_binary([](uint64_t a, uint64_t b) { return a & b; });
    case VirtualExprKind::kOr:
      return fold_binary([](uint64_t a, uint64_t b) { return a | b; });
    case VirtualExprKind::kShl:
      return fold_binary([](uint64_t a, uint64_t b) {
        return b < 64 ? (a << b) : 0ULL;
      });
    case VirtualExprKind::kLShr:
      return fold_binary([](uint64_t a, uint64_t b) {
        return b < 64 ? (a >> b) : 0ULL;
      });
    case VirtualExprKind::kAShr:
      return fold_binary([](uint64_t a, uint64_t b) {
        if (b >= 64)
          return (a & (1ULL << 63)) ? ~0ULL : 0ULL;
        return static_cast<uint64_t>(static_cast<int64_t>(a) >>
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kEq:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a == b);
      });
    case VirtualExprKind::kNe:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a != b);
      });
    case VirtualExprKind::kUlt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a < b);
      });
    case VirtualExprKind::kUle:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a <= b);
      });
    case VirtualExprKind::kUgt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a > b);
      });
    case VirtualExprKind::kUge:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(a >= b);
      });
    case VirtualExprKind::kSlt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) <
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSle:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) <=
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSgt:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) >
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSge:
      return fold_binary([](uint64_t a, uint64_t b) {
        return static_cast<uint64_t>(static_cast<int64_t>(a) >=
                                     static_cast<int64_t>(b));
      });
    case VirtualExprKind::kSelect:
      if (expr.operands.size() != 3)
        return std::nullopt;
      if (auto cond =
              evaluateVirtualExprImpl(expr.operands[0], facts, stack_facts,
                                      visiting_slots, visiting_cells)) {
        return evaluateVirtualExprImpl(expr.operands[*cond ? 1 : 2], facts,
                                       stack_facts, visiting_slots,
                                       visiting_cells);
      }
      return std::nullopt;
    case VirtualExprKind::kPhi:
      if (expr.operands.empty())
        return std::nullopt;
      {
        auto first =
            evaluateVirtualExprImpl(expr.operands.front(), facts, stack_facts,
                                    visiting_slots, visiting_cells);
        if (!first)
          return std::nullopt;
        for (size_t i = 1; i < expr.operands.size(); ++i) {
          auto other = evaluateVirtualExprImpl(expr.operands[i], facts,
                                               stack_facts, visiting_slots,
                                               visiting_cells);
          if (!other || *other != *first)
            return std::nullopt;
        }
        return first;
      }
    case VirtualExprKind::kUnknown:
    case VirtualExprKind::kArgument:
      return std::nullopt;
  }

  return std::nullopt;
}

static std::optional<uint64_t> evaluateVirtualExpr(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts = {}) {
  llvm::SmallDenseSet<unsigned, 8> visiting_slots;
  llvm::SmallDenseSet<unsigned, 8> visiting_cells;
  return evaluateVirtualExprImpl(expr, facts, stack_facts, visiting_slots,
                                 visiting_cells);
}

static VirtualValueExpr summarizeValueExprImpl(
    llvm::Value *V, const llvm::DataLayout &dl,
    llvm::SmallPtrSetImpl<llvm::Value *> &visited, unsigned depth) {
  VirtualValueExpr expr;
  expr.bit_width = getValueBitWidth(V, dl);

  if (depth > 8 || !visited.insert(V).second)
    return expr;

  if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    expr.kind = VirtualExprKind::kConstant;
    expr.complete = true;
    if (ci->getBitWidth() <= 64)
      expr.constant = ci->getZExtValue();
    else
      expr.complete = false;
    return expr;
  }

  if (auto *arg = llvm::dyn_cast<llvm::Argument>(V)) {
    expr.kind = VirtualExprKind::kArgument;
    expr.complete = true;
    expr.argument_index = static_cast<unsigned>(arg->getArgNo());
    return expr;
  }

  if (auto *load = llvm::dyn_cast<llvm::LoadInst>(V)) {
    auto width = dl.getTypeStoreSize(load->getType());
    if (!width.isScalable()) {
      if (auto slot = extractStateSlotSummary(load->getPointerOperand(),
                                              width.getFixedValue(), dl)) {
        expr.kind = VirtualExprKind::kStateSlot;
        expr.complete = true;
        expr.state_base_name = slot->base_name;
        expr.state_offset = slot->offset;
        expr.bit_width = slot->width ? (slot->width * 8u) : expr.bit_width;
        return expr;
      }
      auto pointer_expr =
          summarizeValueExprImpl(load->getPointerOperand(), dl, visited, depth + 1);
      if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                      width.getFixedValue())) {
        expr.kind = VirtualExprKind::kStackCell;
        expr.complete = pointer_expr.complete;
        expr.state_base_name = cell->base_name;
        expr.state_offset = cell->base_offset;
        expr.stack_offset = cell->offset;
        expr.bit_width = cell->width ? (cell->width * 8u) : expr.bit_width;
        return expr;
      }
    }
  }

  if (auto *cast = llvm::dyn_cast<llvm::CastInst>(V)) {
    switch (cast->getOpcode()) {
      case llvm::Instruction::ZExt:
      case llvm::Instruction::SExt:
      case llvm::Instruction::Trunc:
      case llvm::Instruction::BitCast:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::IntToPtr: {
        auto inner =
            summarizeValueExprImpl(cast->getOperand(0), dl, visited, depth + 1);
        inner.bit_width = expr.bit_width ? expr.bit_width : inner.bit_width;
        return inner;
      }
      default:
        break;
    }
  }

  if (auto *call = llvm::dyn_cast<llvm::CallBase>(V)) {
    if (auto *callee = call->getCalledFunction();
        callee && isRemillReadMemoryIntrinsic(*callee) && call->arg_size() >= 2) {
      auto pointer_expr =
          summarizeValueExprImpl(call->getArgOperand(1), dl, visited, depth + 1);
      if (auto cell = extractStackCellSummaryFromExpr(
              pointer_expr, getValueBitWidth(V, dl) / 8)) {
        expr.kind = VirtualExprKind::kStackCell;
        expr.complete = pointer_expr.complete;
        expr.state_base_name = cell->base_name;
        expr.state_offset = cell->base_offset;
        expr.stack_offset = cell->offset;
        expr.bit_width = cell->width ? (cell->width * 8u) : expr.bit_width;
        return expr;
      }
    }
  }

  if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    expr.kind = classifyExprKind(bin->getOpcode());
    if (expr.kind != VirtualExprKind::kUnknown) {
      expr.operands.push_back(
          summarizeValueExprImpl(bin->getOperand(0), dl, visited, depth + 1));
      expr.operands.push_back(
          summarizeValueExprImpl(bin->getOperand(1), dl, visited, depth + 1));
      expr.complete = std::all_of(
          expr.operands.begin(), expr.operands.end(),
          [](const VirtualValueExpr &operand) { return operand.complete; });
      return expr;
    }
  }

  if (auto *select = llvm::dyn_cast<llvm::SelectInst>(V)) {
    expr.kind = VirtualExprKind::kSelect;
    expr.operands.push_back(
        summarizeValueExprImpl(select->getCondition(), dl, visited, depth + 1));
    expr.operands.push_back(
        summarizeValueExprImpl(select->getTrueValue(), dl, visited, depth + 1));
    expr.operands.push_back(
        summarizeValueExprImpl(select->getFalseValue(), dl, visited, depth + 1));
    expr.complete = std::all_of(
        expr.operands.begin(), expr.operands.end(),
        [](const VirtualValueExpr &operand) { return operand.complete; });
    return expr;
  }

  if (auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(V)) {
    expr.kind = classifyICmpPredicate(icmp->getPredicate());
    expr.bit_width = 1;
    if (expr.kind != VirtualExprKind::kUnknown) {
      expr.operands.push_back(
          summarizeValueExprImpl(icmp->getOperand(0), dl, visited, depth + 1));
      expr.operands.push_back(
          summarizeValueExprImpl(icmp->getOperand(1), dl, visited, depth + 1));
      expr.complete = std::all_of(
          expr.operands.begin(), expr.operands.end(),
          [](const VirtualValueExpr &operand) { return operand.complete; });
      return expr;
    }
  }

  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(V)) {
    expr.kind = VirtualExprKind::kPhi;
    unsigned limit = std::min<unsigned>(phi->getNumIncomingValues(), 4);
    for (unsigned i = 0; i < limit; ++i) {
      expr.operands.push_back(summarizeValueExprImpl(phi->getIncomingValue(i),
                                                     dl, visited, depth + 1));
    }
    expr.complete =
        !expr.operands.empty() &&
        std::all_of(expr.operands.begin(), expr.operands.end(),
                    [](const VirtualValueExpr &operand) {
                      return operand.complete;
                    });
    return expr;
  }

  return expr;
}

static VirtualValueExpr summarizeValueExpr(llvm::Value *V,
                                           const llvm::DataLayout &dl) {
  llvm::SmallPtrSet<llvm::Value *, 16> visited;
  return summarizeValueExprImpl(V, dl, visited, 0);
}

static void collectExprSlotIds(const VirtualValueExpr &expr,
                               std::set<unsigned> &ids) {
  if (expr.slot_id.has_value())
    ids.insert(*expr.slot_id);
  for (const auto &operand : expr.operands)
    collectExprSlotIds(operand, ids);
}

static void collectExprStackCellIds(const VirtualValueExpr &expr,
                                    std::set<unsigned> &ids) {
  if (expr.stack_cell_id.has_value())
    ids.insert(*expr.stack_cell_id);
  for (const auto &operand : expr.operands)
    collectExprStackCellIds(operand, ids);
}

static void collectExprReferencedStackCells(
    const VirtualValueExpr &expr,
    std::vector<VirtualStackCellSummary> &cells) {
  auto expr_width_bytes = [](const VirtualValueExpr &value) {
    return value.bit_width ? std::max(1u, value.bit_width / 8u) : 8u;
  };
  if (expr.kind == VirtualExprKind::kStackCell && expr.state_base_name.has_value() &&
      expr.state_offset.has_value() && expr.stack_offset.has_value()) {
    llvm::StringRef base_name = *expr.state_base_name;
    const bool from_argument = base_name.starts_with("arg");
    cells.push_back(VirtualStackCellSummary{
        *expr.state_base_name,
        *expr.state_offset,
        expr_width_bytes(expr),
        *expr.stack_offset,
        expr_width_bytes(expr),
        1,
        0,
        from_argument,
        !from_argument,
        std::nullopt,
        std::nullopt,
    });
  }
  for (const auto &operand : expr.operands)
    collectExprReferencedStackCells(operand, cells);
}

static void collectExprReferencedStateSlots(
    const VirtualValueExpr &expr,
    std::vector<VirtualStateSlotSummary> &slots) {
  auto expr_width_bytes = [](const VirtualValueExpr &value) {
    return value.bit_width ? std::max(1u, value.bit_width / 8u) : 8u;
  };
  if (expr.kind == VirtualExprKind::kStateSlot && expr.state_base_name.has_value() &&
      expr.state_offset.has_value()) {
    llvm::StringRef base_name = *expr.state_base_name;
    const bool from_argument = base_name.starts_with("arg");
    slots.push_back(VirtualStateSlotSummary{
        *expr.state_base_name,
        *expr.state_offset,
        expr_width_bytes(expr),
        1,
        0,
        from_argument,
        !from_argument,
        std::nullopt,
    });
  }
  for (const auto &operand : expr.operands)
    collectExprReferencedStateSlots(operand, slots);
}

static VirtualHandlerSummary summarizeFunction(llvm::Function &F) {
  constexpr unsigned kMaxSummaryStackCells = 16;

  VirtualHandlerSummary summary;
  summary.function_name = F.getName().str();
  uint64_t entry_va = extractLiftedPCFromName(F.getName());
  if (entry_va != 0)
    summary.entry_va = entry_va;
  summary.is_output_root = F.hasFnAttribute("omill.output_root");
  summary.is_specialized = F.hasFnAttribute("omill.virtual_specialized");
  summary.specialization_root_va =
      extractHexAttr(F, "omill.virtual_specialization.root_va");
  summary.specialization_facts = parseSpecializationFacts(F);
  summary.specialization_stack_facts = parseSpecializationStackFacts(F);

  const llvm::DataLayout &dl = F.getParent()->getDataLayout();
  std::vector<std::tuple<std::string, int64_t, unsigned, unsigned, unsigned,
                         bool, bool>>
      slot_accum;
  std::vector<std::tuple<std::string, int64_t, unsigned, int64_t, unsigned,
                         unsigned, unsigned, bool, bool>>
      stack_cell_accum;

  auto recordSlot = [&](const VirtualStateSlotSummary &slot, bool is_store) {
    auto it = std::find_if(slot_accum.begin(), slot_accum.end(),
                           [&](const auto &current) {
                             return std::get<0>(current) == slot.base_name &&
                                    std::get<1>(current) == slot.offset &&
                                    std::get<2>(current) == slot.width &&
                                    std::get<5>(current) == slot.from_argument &&
                                    std::get<6>(current) == slot.from_alloca;
                           });
    if (it == slot_accum.end()) {
      slot_accum.emplace_back(slot.base_name, slot.offset, slot.width,
                              is_store ? 0u : 1u, is_store ? 1u : 0u,
                              slot.from_argument, slot.from_alloca);
      return;
    }
    if (is_store)
      ++std::get<4>(*it);
    else
      ++std::get<3>(*it);
  };

  auto recordStackCell = [&](const VirtualStackCellSummary &cell,
                             bool is_store) {
    auto it = std::find_if(stack_cell_accum.begin(), stack_cell_accum.end(),
                           [&](const auto &current) {
                             return std::get<0>(current) == cell.base_name &&
                                    std::get<1>(current) == cell.base_offset &&
                                    std::get<2>(current) == cell.base_width &&
                                    std::get<3>(current) == cell.offset &&
                                    std::get<4>(current) == cell.width &&
                                    std::get<7>(current) ==
                                        cell.base_from_argument &&
                                    std::get<8>(current) ==
                                        cell.base_from_alloca;
                           });
    if (it == stack_cell_accum.end()) {
      if (stack_cell_accum.size() >= kMaxSummaryStackCells) {
        summary.stack_memory_budget_exceeded = true;
        return false;
      }
      stack_cell_accum.emplace_back(
          cell.base_name, cell.base_offset, cell.base_width, cell.offset,
          cell.width, is_store ? 0u : 1u, is_store ? 1u : 0u,
          cell.base_from_argument, cell.base_from_alloca);
      return true;
    }
    if (is_store)
      ++std::get<6>(*it);
    else
      ++std::get<5>(*it);
    return true;
  };

  auto recordExprStackCells = [&](const VirtualValueExpr &expr) {
    unsigned expr_width = expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u;
    if (auto cell = extractStackCellSummaryFromExpr(expr, expr_width))
      recordStackCell(*cell, /*is_store=*/false);
    std::vector<VirtualStackCellSummary> referenced_cells;
    collectExprReferencedStackCells(expr, referenced_cells);
    for (const auto &cell : referenced_cells)
      recordStackCell(cell, /*is_store=*/false);
  };

  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *load = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        auto width = dl.getTypeStoreSize(load->getType());
        if (width.isScalable())
          continue;
        if (auto slot = extractStateSlotSummary(load->getPointerOperand(),
                                                width.getFixedValue(), dl)) {
          recordSlot(*slot, /*is_store=*/false);
        } else {
          auto pointer_expr = summarizeValueExpr(load->getPointerOperand(), dl);
          if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                          width.getFixedValue())) {
            recordStackCell(*cell, /*is_store=*/false);
          } else if (pointer_expr.kind == VirtualExprKind::kStateSlot ||
                     (pointer_expr.kind == VirtualExprKind::kAdd &&
                      llvm::any_of(pointer_expr.operands,
                                   [](const VirtualValueExpr &operand) {
                                     return operand.kind ==
                                            VirtualExprKind::kStateSlot;
                                   })) ||
                     (pointer_expr.kind == VirtualExprKind::kSub &&
                      !pointer_expr.operands.empty() &&
                      pointer_expr.operands.front().kind ==
                          VirtualExprKind::kStateSlot)) {
            summary.has_unsupported_stack_memory = true;
          }
        }
        continue;
      }

      if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto width = dl.getTypeStoreSize(store->getValueOperand()->getType());
        if (width.isScalable())
          continue;
        if (auto slot = extractStateSlotSummary(store->getPointerOperand(),
                                                width.getFixedValue(), dl)) {
          recordSlot(*slot, /*is_store=*/true);
          auto value_expr = summarizeValueExpr(store->getValueOperand(), dl);
          recordExprStackCells(value_expr);
          summary.state_transfers.push_back(
              VirtualStateTransferSummary{*slot, std::move(value_expr)});
        } else {
          auto pointer_expr = summarizeValueExpr(store->getPointerOperand(), dl);
          if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                          width.getFixedValue())) {
            if (recordStackCell(*cell, /*is_store=*/true)) {
              auto value_expr = summarizeValueExpr(store->getValueOperand(), dl);
              recordExprStackCells(value_expr);
              summary.stack_transfers.push_back(
                  VirtualStackTransferSummary{*cell, std::move(value_expr)});
            }
          } else if (pointer_expr.kind == VirtualExprKind::kStateSlot ||
                     (pointer_expr.kind == VirtualExprKind::kAdd &&
                      llvm::any_of(pointer_expr.operands,
                                   [](const VirtualValueExpr &operand) {
                                     return operand.kind ==
                                            VirtualExprKind::kStateSlot;
                                   })) ||
                     (pointer_expr.kind == VirtualExprKind::kSub &&
                      !pointer_expr.operands.empty() &&
                      pointer_expr.operands.front().kind ==
                          VirtualExprKind::kStateSlot)) {
            summary.has_unsupported_stack_memory = true;
          }
        }
        continue;
      }

      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;

      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;

      for (llvm::Value *arg : call->args()) {
        auto arg_expr = summarizeValueExpr(arg, dl);
        recordExprStackCells(arg_expr);
      }

      if (isRemillWriteMemoryIntrinsic(*callee) && call->arg_size() >= 3) {
        unsigned width_bits =
            remillMemoryBitWidth(callee->getName()).value_or(0);
        unsigned width_bytes = width_bits / 8;
        auto address_expr = summarizeValueExpr(call->getArgOperand(1), dl);
        if (auto cell =
                extractStackCellSummaryFromExpr(address_expr, width_bytes)) {
          if (recordStackCell(*cell, /*is_store=*/true)) {
            auto value_expr = summarizeValueExpr(call->getArgOperand(2), dl);
            recordExprStackCells(value_expr);
            summary.stack_transfers.push_back(VirtualStackTransferSummary{
                *cell, std::move(value_expr)});
          }
        } else if (address_expr.kind == VirtualExprKind::kStateSlot ||
                   address_expr.kind == VirtualExprKind::kArgument ||
                   (address_expr.kind == VirtualExprKind::kAdd &&
                    llvm::any_of(address_expr.operands,
                                 [](const VirtualValueExpr &operand) {
                                   return operand.kind ==
                                              VirtualExprKind::kStateSlot ||
                                          operand.kind ==
                                              VirtualExprKind::kArgument;
                                 })) ||
                   (address_expr.kind == VirtualExprKind::kSub &&
                    !address_expr.operands.empty() &&
                    (address_expr.operands.front().kind ==
                         VirtualExprKind::kStateSlot ||
                     address_expr.operands.front().kind ==
                         VirtualExprKind::kArgument))) {
          summary.has_unsupported_stack_memory = true;
        }
        continue;
      }

      if (isDispatchIntrinsic(*callee)) {
        if (callee->getName().ends_with("call"))
          ++summary.dispatch_call_count;
        else
          ++summary.dispatch_jump_count;
        if (call->arg_size() >= 2) {
          VirtualDispatchSummary dispatch;
          dispatch.is_jump = callee->getName().ends_with("jump");
          dispatch.target = summarizeValueExpr(call->getArgOperand(1), dl);
          summary.dispatches.push_back(std::move(dispatch));
        }
        continue;
      }

      if (!isBoundaryFunction(*callee))
        goto non_boundary_call;

      ++summary.protected_boundary_call_count;
      summary.called_boundaries.push_back(callee->getName().str());
      continue;

    non_boundary_call:
      if (isCallSiteHelper(*callee) && call->arg_size() >= 3) {
        VirtualCallSiteSummary callsite;
        callsite.is_call = true;
        callsite.target = summarizeValueExpr(call->getArgOperand(2), dl);
        summary.callsites.push_back(std::move(callsite));
      }
      if (!callee->isDeclaration())
        summary.direct_callees.push_back(callee->getName().str());
    }
  }

  for (const auto &slot : slot_accum) {
    summary.state_slots.push_back(VirtualStateSlotSummary{
        std::get<0>(slot),
        std::get<1>(slot),
        std::get<2>(slot),
        std::get<3>(slot),
        std::get<4>(slot),
        std::get<5>(slot),
        std::get<6>(slot),
        std::nullopt,
    });
  }

  for (const auto &cell : stack_cell_accum) {
    summary.stack_cells.push_back(VirtualStackCellSummary{
        std::get<0>(cell),
        std::get<1>(cell),
        std::get<2>(cell),
        std::get<3>(cell),
        std::get<4>(cell),
        std::get<5>(cell),
        std::get<6>(cell),
        std::get<7>(cell),
        std::get<8>(cell),
        std::nullopt,
        std::nullopt,
    });
  }

  std::sort(summary.called_boundaries.begin(), summary.called_boundaries.end());
  summary.called_boundaries.erase(
      std::unique(summary.called_boundaries.begin(),
                  summary.called_boundaries.end()),
      summary.called_boundaries.end());
  std::sort(summary.direct_callees.begin(), summary.direct_callees.end());
  summary.direct_callees.erase(
      std::unique(summary.direct_callees.begin(), summary.direct_callees.end()),
      summary.direct_callees.end());

  const bool has_dispatch =
      (summary.dispatch_call_count + summary.dispatch_jump_count) != 0;
  const bool has_boundary_call = summary.protected_boundary_call_count != 0;
  const bool has_state_shape = summary.state_slots.size() >= 2;
  summary.is_candidate = has_state_shape && (has_dispatch || has_boundary_call);
  return summary;
}

struct SlotKey {
  std::string base_name;
  int64_t offset = 0;
  unsigned width = 0;
  bool from_argument = false;
  bool from_alloca = false;

  auto tie() const {
    return std::tie(base_name, offset, width, from_argument, from_alloca);
  }

  bool operator<(const SlotKey &other) const { return tie() < other.tie(); }
};

struct StackCellKey {
  SlotKey base_slot;
  int64_t cell_offset = 0;
  unsigned width = 0;

  auto tie() const { return std::tie(base_slot, cell_offset, width); }

  bool operator<(const StackCellKey &other) const {
    return tie() < other.tie();
  }
};

static SlotKey slotKeyForSummary(const VirtualStateSlotSummary &slot) {
  return SlotKey{slot.base_name, slot.offset, slot.width, slot.from_argument,
                 slot.from_alloca};
}

static SlotKey slotKeyForExpr(const VirtualValueExpr &expr) {
  auto base_name = expr.state_base_name.value_or("state");
  bool from_argument = base_name.rfind("arg", 0) == 0;
  unsigned width_bytes = expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 0u;
  return SlotKey{expr.state_base_name.value_or("state"),
                 expr.state_offset.value_or(0), width_bytes,
                 from_argument, !from_argument};
}

using BooleanSlotExprKey = std::tuple<std::string, int64_t, bool, bool>;

static std::optional<BooleanSlotExprKey> booleanSlotExprKeyForExpr(
    const VirtualValueExpr &expr) {
  if (expr.kind != VirtualExprKind::kStateSlot || !expr.state_base_name ||
      !expr.state_offset) {
    return std::nullopt;
  }
  bool from_argument = expr.state_base_name->rfind("arg", 0) == 0;
  return BooleanSlotExprKey{*expr.state_base_name, *expr.state_offset,
                            from_argument, !from_argument};
}

static StackCellKey stackCellKeyForSummary(const VirtualStackCellSummary &cell) {
  return StackCellKey{
      SlotKey{cell.base_name, cell.base_offset, cell.base_width,
              cell.base_from_argument, cell.base_from_alloca},
      cell.offset, cell.width};
}

static std::optional<unsigned> findEquivalentArgumentStackCellId(
    int64_t base_offset, unsigned base_width, bool base_from_argument,
    bool base_from_alloca, int64_t cell_offset, unsigned width,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  if (!base_from_argument || base_from_alloca)
    return std::nullopt;

  std::optional<unsigned> mapped_cell_id;
  for (const auto &[cell_key, cell_id] : stack_cell_ids) {
    if (!cell_key.base_slot.from_argument || cell_key.base_slot.from_alloca)
      continue;
    if (cell_key.base_slot.offset != base_offset ||
        cell_key.base_slot.width != base_width ||
        cell_key.cell_offset != cell_offset || cell_key.width != width) {
      continue;
    }
    if (mapped_cell_id && *mapped_cell_id != cell_id)
      return std::nullopt;
    mapped_cell_id = cell_id;
  }
  return mapped_cell_id;
}

static void annotateExprSlots(
    VirtualValueExpr &expr, const std::map<SlotKey, unsigned> &slot_ids) {
  if (expr.kind == VirtualExprKind::kStateSlot) {
    auto it = slot_ids.find(slotKeyForExpr(expr));
    if (it != slot_ids.end())
      expr.slot_id = it->second;
  }
  for (auto &operand : expr.operands)
    annotateExprSlots(operand, slot_ids);
}

static void annotateExprStackCells(
    VirtualValueExpr &expr, const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<SlotKey, unsigned> &slot_ids) {
  if (expr.kind == VirtualExprKind::kStackCell && expr.state_base_name.has_value() &&
      expr.state_offset.has_value() && expr.stack_offset.has_value()) {
    llvm::StringRef base_name = *expr.state_base_name;
    bool from_argument = base_name.starts_with("arg");
    auto base_slot_key =
        SlotKey{*expr.state_base_name, *expr.state_offset,
                expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u,
                from_argument,
                !from_argument};
    auto cell_key = StackCellKey{base_slot_key, *expr.stack_offset,
                                 expr.bit_width ? std::max(1u, expr.bit_width / 8u)
                                                : 8u};
    auto cell_it = stack_cell_ids.find(cell_key);
    if (cell_it == stack_cell_ids.end()) {
      cell_it = llvm::find_if(stack_cell_ids, [&](const auto &entry) {
        return entry.first.base_slot.base_name == base_slot_key.base_name &&
               entry.first.base_slot.offset == base_slot_key.offset &&
               entry.first.base_slot.from_argument ==
                   base_slot_key.from_argument &&
               entry.first.base_slot.from_alloca ==
                   base_slot_key.from_alloca &&
               entry.first.cell_offset == *expr.stack_offset;
      });
    }
    if (cell_it != stack_cell_ids.end()) {
      expr.stack_cell_id = cell_it->second;
    } else if (auto fallback_cell_id = findEquivalentArgumentStackCellId(
                   base_slot_key.offset, base_slot_key.width,
                   base_slot_key.from_argument, base_slot_key.from_alloca,
                   *expr.stack_offset,
                   expr.bit_width ? std::max(1u, expr.bit_width / 8u) : 8u,
                   stack_cell_ids)) {
      expr.stack_cell_id = *fallback_cell_id;
    }
    auto slot_it = slot_ids.find(base_slot_key);
    if (slot_it != slot_ids.end())
      expr.slot_id = slot_it->second;
  }
  for (auto &operand : expr.operands)
    annotateExprStackCells(operand, stack_cell_ids, slot_ids);
}

static uint64_t bitMask(unsigned bits) {
  if (bits == 0 || bits >= 64)
    return ~0ULL;
  return (1ULL << bits) - 1;
}

static bool exprEquals(const VirtualValueExpr &lhs, const VirtualValueExpr &rhs) {
  if (lhs.kind != rhs.kind || lhs.bit_width != rhs.bit_width ||
      lhs.complete != rhs.complete || lhs.constant != rhs.constant ||
      lhs.argument_index != rhs.argument_index || lhs.slot_id != rhs.slot_id ||
      lhs.state_base_name != rhs.state_base_name ||
      lhs.state_offset != rhs.state_offset ||
      lhs.stack_cell_id != rhs.stack_cell_id ||
      lhs.stack_offset != rhs.stack_offset ||
      lhs.operands.size() != rhs.operands.size()) {
    return false;
  }

  for (size_t i = 0; i < lhs.operands.size(); ++i) {
    if (!exprEquals(lhs.operands[i], rhs.operands[i]))
      return false;
  }
  return true;
}

static bool slotFactMapEquals(const std::map<unsigned, VirtualValueExpr> &lhs,
                              const std::map<unsigned, VirtualValueExpr> &rhs) {
  if (lhs.size() != rhs.size())
    return false;
  auto lit = lhs.begin();
  auto rit = rhs.begin();
  for (; lit != lhs.end(); ++lit, ++rit) {
    if (lit->first != rit->first || !exprEquals(lit->second, rit->second))
      return false;
  }
  return true;
}

static bool stackFactMapEquals(const std::map<unsigned, VirtualValueExpr> &lhs,
                               const std::map<unsigned, VirtualValueExpr> &rhs) {
  return slotFactMapEquals(lhs, rhs);
}

static bool isUnknownLikeExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kUnknown)
    return true;
  if (expr.kind != VirtualExprKind::kPhi || expr.operands.empty())
    return false;
  return llvm::all_of(expr.operands, isUnknownLikeExpr);
}

static bool containsStateSlotExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kStateSlot)
    return true;
  return llvm::any_of(expr.operands, containsStateSlotExpr);
}

static bool containsStackCellExpr(const VirtualValueExpr &expr) {
  if (expr.kind == VirtualExprKind::kStackCell)
    return true;
  return llvm::any_of(expr.operands, containsStackCellExpr);
}

static unsigned exprByteWidth(const VirtualValueExpr &expr,
                              unsigned fallback = 8) {
  return expr.bit_width ? std::max(1u, expr.bit_width / 8u) : fallback;
}

static unsigned countSymbolicRefs(const VirtualValueExpr &expr) {
  unsigned refs =
      (expr.kind == VirtualExprKind::kStateSlot ||
       expr.kind == VirtualExprKind::kStackCell ||
       expr.kind == VirtualExprKind::kArgument)
          ? 1u
          : 0u;
  for (const auto &operand : expr.operands)
    refs += countSymbolicRefs(operand);
  return refs;
}

static bool isBoundedFactExpr(const VirtualValueExpr &expr,
                              bool allow_arguments, unsigned depth = 0) {
  if (depth > 4)
    return false;

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
    case VirtualExprKind::kStateSlot:
    case VirtualExprKind::kStackCell:
      return true;
    case VirtualExprKind::kArgument:
      return allow_arguments;
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
      if (expr.operands.size() != 2)
        return false;
      return (expr.operands[0].constant.has_value() &&
              isBoundedFactExpr(expr.operands[1], allow_arguments, depth + 1)) ||
             (expr.operands[1].constant.has_value() &&
              isBoundedFactExpr(expr.operands[0], allow_arguments, depth + 1));
    case VirtualExprKind::kPhi:
      return !expr.operands.empty() && expr.operands.size() <= 4 &&
             std::all_of(expr.operands.begin(), expr.operands.end(),
                         [&](const VirtualValueExpr &operand) {
                           return isBoundedFactExpr(operand, allow_arguments,
                                                    depth + 1);
                         });
    default:
      return false;
  }
}

static bool isBoundedArgumentFactExpr(const VirtualValueExpr &expr,
                                      unsigned depth = 0) {
  return isBoundedFactExpr(expr, /*allow_arguments=*/true, depth);
}

static bool isBoundedStateProvenanceExpr(const VirtualValueExpr &expr,
                                         unsigned depth = 0) {
  return isBoundedFactExpr(expr, /*allow_arguments=*/false, depth);
}

static bool isIdentitySlotExpr(const VirtualValueExpr &expr, unsigned slot_id) {
  return expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value() &&
         *expr.slot_id == slot_id;
}

static bool isIdentityStackCellExpr(const VirtualValueExpr &expr,
                                    unsigned cell_id) {
  return expr.kind == VirtualExprKind::kStackCell &&
         expr.stack_cell_id.has_value() && *expr.stack_cell_id == cell_id;
}

static bool isSimpleRemappableFactExpr(const VirtualValueExpr &expr,
                                       unsigned depth = 0) {
  return isBoundedFactExpr(expr, /*allow_arguments=*/false, depth);
}

static bool containsCallerLocalAllocaStateExpr(const VirtualValueExpr &expr) {
  if ((expr.kind == VirtualExprKind::kStateSlot ||
       expr.kind == VirtualExprKind::kStackCell) &&
      expr.state_base_name.has_value() &&
      !llvm::StringRef(*expr.state_base_name).starts_with("arg")) {
    return true;
  }

  return llvm::any_of(expr.operands, [](const VirtualValueExpr &operand) {
    return containsCallerLocalAllocaStateExpr(operand);
  });
}

static bool isGloballyMergeableStateFactExpr(const VirtualValueExpr &expr,
                                             bool allow_arguments) {
  return isBoundedFactExpr(expr, allow_arguments) &&
         !containsCallerLocalAllocaStateExpr(expr);
}

static VirtualValueExpr unknownExpr(unsigned bits = 0) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kUnknown;
  expr.bit_width = bits;
  expr.complete = false;
  return expr;
}

static VirtualValueExpr constantExpr(uint64_t value, unsigned bits) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kConstant;
  expr.bit_width = bits;
  expr.complete = true;
  expr.constant = value & bitMask(bits);
  return expr;
}

struct EntryPreludeCallInfo {
  uint64_t call_pc = 0;
  uint64_t target_pc = 0;
  uint64_t continuation_pc = 0;
};

static VirtualValueExpr argumentExpr(unsigned index, unsigned bits = 64) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kArgument;
  expr.bit_width = bits;
  expr.complete = true;
  expr.argument_index = index;
  return expr;
}

static std::optional<EntryPreludeCallInfo> detectEntryPreludeDirectCall(
    const BinaryMemoryMap &binary_memory, uint64_t entry_va) {
  if (entry_va < 5)
    return std::nullopt;

  uint8_t bytes[5] = {};
  auto call_pc = entry_va - 5;
  if (!binary_memory.read(call_pc, bytes, sizeof(bytes)) || bytes[0] != 0xE8)
    return std::nullopt;

  int32_t rel = 0;
  std::memcpy(&rel, bytes + 1, sizeof(rel));

  auto continuation_pc = call_pc + 5;
  auto target_pc = static_cast<uint64_t>(
      static_cast<int64_t>(continuation_pc) + static_cast<int64_t>(rel));
  if (continuation_pc != entry_va || target_pc == 0)
    return std::nullopt;

  return EntryPreludeCallInfo{call_pc, target_pc, continuation_pc};
}

static std::optional<VirtualValueExpr> mergeIncomingExpr(
    const VirtualValueExpr &existing, const VirtualValueExpr &incoming) {
  if (exprEquals(existing, incoming))
    return existing;

  if (existing.bit_width != 0 && incoming.bit_width != 0 &&
      existing.bit_width != incoming.bit_width) {
    return std::nullopt;
  }

  llvm::SmallVector<VirtualValueExpr, 4> choices;
  auto append_unique = [&](const VirtualValueExpr &expr) {
    for (const auto &choice : choices) {
      if (exprEquals(choice, expr))
        return;
    }
    choices.push_back(expr);
  };

  if (existing.kind == VirtualExprKind::kPhi) {
    for (const auto &operand : existing.operands)
      append_unique(operand);
  } else {
    append_unique(existing);
  }

  if (incoming.kind == VirtualExprKind::kPhi) {
    for (const auto &operand : incoming.operands)
      append_unique(operand);
  } else {
    append_unique(incoming);
  }

  if (choices.empty() || choices.size() > 4)
    return std::nullopt;

  VirtualValueExpr merged;
  merged.kind = VirtualExprKind::kPhi;
  merged.bit_width = existing.bit_width ? existing.bit_width : incoming.bit_width;
  merged.complete = std::all_of(
      choices.begin(), choices.end(),
      [](const VirtualValueExpr &choice) { return choice.complete; });
  merged.operands.assign(choices.begin(), choices.end());
  return merged;
}

static bool collectEvaluatedTargetChoicesImpl(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    const llvm::DenseSet<unsigned> *boolean_slot_ids,
    const std::set<BooleanSlotExprKey> *boolean_slot_expr_keys,
    llvm::SmallDenseSet<unsigned, 8> &visiting_slots,
    llvm::SmallDenseSet<unsigned, 8> &visiting_cells,
    llvm::SmallVectorImpl<uint64_t> &pcs, unsigned depth) {
  if (depth > 4 || pcs.size() > 4)
    return false;

  auto append_pc = [&](uint64_t pc) {
    if (!llvm::is_contained(pcs, pc))
      pcs.push_back(pc);
    return pcs.size() <= 4;
  };

  auto lookup_slot = [&](unsigned slot_id) {
    auto it = std::find_if(facts.begin(), facts.end(),
                           [&](const VirtualSlotFact &fact) {
                             return fact.slot_id == slot_id;
                           });
    if (it == facts.end()) {
      if (boolean_slot_ids && boolean_slot_ids->contains(slot_id))
        return append_pc(0) && append_pc(1);
      return false;
    }
    if (!visiting_slots.insert(slot_id).second)
      return false;
    bool ok = collectEvaluatedTargetChoicesImpl(
        it->value, facts, stack_facts, boolean_slot_ids,
        boolean_slot_expr_keys, visiting_slots, visiting_cells, pcs,
        depth + 1);
    visiting_slots.erase(slot_id);
    if (!ok && boolean_slot_ids && boolean_slot_ids->contains(slot_id) &&
        isUnknownLikeExpr(it->value)) {
      return append_pc(0) && append_pc(1);
    }
    return ok;
  };

  auto lookup_stack = [&](unsigned cell_id) {
    auto it = std::find_if(stack_facts.begin(), stack_facts.end(),
                           [&](const VirtualStackFact &fact) {
                             return fact.cell_id == cell_id;
                           });
    if (it == stack_facts.end() || !visiting_cells.insert(cell_id).second)
      return false;
    bool ok = collectEvaluatedTargetChoicesImpl(
        it->value, facts, stack_facts, boolean_slot_ids,
        boolean_slot_expr_keys, visiting_slots, visiting_cells, pcs,
        depth + 1);
    visiting_cells.erase(cell_id);
    return ok;
  };

  auto collect_offset_choices =
      [&](const VirtualValueExpr &base_expr, uint64_t constant,
          bool is_sub) -> bool {
    llvm::SmallVector<uint64_t, 4> base_pcs;
    if (!collectEvaluatedTargetChoicesImpl(base_expr, facts, stack_facts,
                                           boolean_slot_ids,
                                           boolean_slot_expr_keys,
                                           visiting_slots, visiting_cells,
                                           base_pcs, depth + 1)) {
      return false;
    }
    for (uint64_t base_pc : base_pcs) {
      uint64_t resolved = is_sub ? (base_pc - constant) : (base_pc + constant);
      if (!append_pc(resolved))
        return false;
    }
    return true;
  };

  if (auto resolved =
          evaluateVirtualExprImpl(expr, facts, stack_facts, visiting_slots,
                                  visiting_cells)) {
    return append_pc(*resolved);
  }

  switch (expr.kind) {
    case VirtualExprKind::kConstant:
      return expr.constant.has_value() && append_pc(*expr.constant);
    case VirtualExprKind::kStateSlot:
      if (expr.slot_id.has_value())
        return lookup_slot(*expr.slot_id);
      if (boolean_slot_expr_keys) {
        auto key = booleanSlotExprKeyForExpr(expr);
        if (key && boolean_slot_expr_keys->find(*key) !=
                       boolean_slot_expr_keys->end())
          return append_pc(0) && append_pc(1);
      }
      return false;
    case VirtualExprKind::kStackCell:
      return expr.stack_cell_id.has_value() && lookup_stack(*expr.stack_cell_id);
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
      if (expr.operands.size() != 2)
        return false;
      if (expr.kind == VirtualExprKind::kAdd &&
          expr.operands[0].constant.has_value()) {
        return collect_offset_choices(expr.operands[1],
                                      *expr.operands[0].constant,
                                      /*is_sub=*/false);
      }
      if (expr.operands[1].constant.has_value())
        return collect_offset_choices(expr.operands[0],
                                      *expr.operands[1].constant,
                                      /*is_sub=*/expr.kind ==
                                          VirtualExprKind::kSub);
      return false;
    case VirtualExprKind::kPhi:
      if (expr.operands.empty() || expr.operands.size() > 4)
        return false;
      for (const auto &operand : expr.operands) {
        if (!collectEvaluatedTargetChoicesImpl(operand, facts, stack_facts,
                                               boolean_slot_ids,
                                               boolean_slot_expr_keys,
                                               visiting_slots, visiting_cells,
                                               pcs, depth + 1)) {
          return false;
        }
      }
      return !pcs.empty() && pcs.size() <= 4;
    default:
      return false;
  }
}

static bool collectEvaluatedTargetChoices(const VirtualValueExpr &expr,
                                          const std::vector<VirtualSlotFact> &facts,
                                          const std::vector<VirtualStackFact> &stack_facts,
                                          const llvm::DenseSet<unsigned> *boolean_slot_ids,
                                          const std::set<BooleanSlotExprKey> *boolean_slot_expr_keys,
                                          llvm::SmallVectorImpl<uint64_t> &pcs) {
  llvm::SmallDenseSet<unsigned, 8> visiting_slots;
  llvm::SmallDenseSet<unsigned, 8> visiting_cells;
  return collectEvaluatedTargetChoicesImpl(expr, facts, stack_facts,
                                           boolean_slot_ids,
                                           boolean_slot_expr_keys,
                                           visiting_slots, visiting_cells, pcs,
                                           /*depth=*/0) &&
         pcs.size() >= 2;
}

static VirtualValueExpr specializeExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> *incoming_stack = nullptr,
    const std::map<unsigned, VirtualValueExpr> *incoming_args = nullptr) {
  if (expr.kind == VirtualExprKind::kArgument &&
      expr.argument_index.has_value() && incoming_args) {
    auto it = incoming_args->find(*expr.argument_index);
    if (it != incoming_args->end())
      return it->second;
    return expr;
  }
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value()) {
    auto it = incoming.find(*expr.slot_id);
    if (it != incoming.end())
      return it->second;
    return expr;
  }
  if (expr.kind == VirtualExprKind::kStackCell && expr.stack_cell_id.has_value() &&
      incoming_stack) {
    auto it = incoming_stack->find(*expr.stack_cell_id);
    if (it != incoming_stack->end())
      return it->second;
    return expr;
  }

  VirtualValueExpr result = expr;
  result.operands.clear();
  for (const auto &operand : expr.operands)
    result.operands.push_back(
        specializeExpr(operand, incoming, incoming_stack, incoming_args));

  auto fold_binary = [&](auto fn) -> std::optional<VirtualValueExpr> {
    if (result.operands.size() != 2)
      return std::nullopt;
    const auto &lhs = result.operands[0];
    const auto &rhs = result.operands[1];
    if (!lhs.constant.has_value() || !rhs.constant.has_value())
      return std::nullopt;
    return constantExpr(
        fn(*lhs.constant, *rhs.constant) & bitMask(result.bit_width),
        result.bit_width);
  };

  switch (result.kind) {
    case VirtualExprKind::kAdd:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a + b; }))
        return *folded;
      break;
    case VirtualExprKind::kSub:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a - b; }))
        return *folded;
      break;
    case VirtualExprKind::kMul:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a * b; }))
        return *folded;
      break;
    case VirtualExprKind::kXor:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a ^ b; }))
        return *folded;
      break;
    case VirtualExprKind::kAnd:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a & b; }))
        return *folded;
      break;
    case VirtualExprKind::kOr:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) { return a | b; }))
        return *folded;
      break;
    case VirtualExprKind::kShl:
      if (auto folded =
              fold_binary([](uint64_t a, uint64_t b) { return (b < 64) ? (a << b) : 0ULL; }))
        return *folded;
      break;
    case VirtualExprKind::kLShr:
      if (auto folded =
              fold_binary([](uint64_t a, uint64_t b) { return (b < 64) ? (a >> b) : 0ULL; }))
        return *folded;
      break;
    case VirtualExprKind::kAShr:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            if (b >= 64)
              return (a & (1ULL << 63)) ? ~0ULL : 0ULL;
            return static_cast<uint64_t>(static_cast<int64_t>(a) >>
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSelect:
      if (result.operands.size() == 3 &&
          result.operands[0].constant.has_value()) {
        return result.operands[*result.operands[0].constant ? 1 : 2];
      }
      break;
    case VirtualExprKind::kEq:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a == b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kNe:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a != b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUlt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a < b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUle:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a <= b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUgt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a > b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kUge:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(a >= b);
          }))
        return *folded;
      break;
    case VirtualExprKind::kSlt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) <
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSle:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) <=
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSgt:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) >
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kSge:
      if (auto folded = fold_binary([](uint64_t a, uint64_t b) {
            return static_cast<uint64_t>(static_cast<int64_t>(a) >=
                                         static_cast<int64_t>(b));
          }))
        return *folded;
      break;
    case VirtualExprKind::kPhi:
      if (!result.operands.empty()) {
        bool same = std::all_of(result.operands.begin() + 1,
                                result.operands.end(),
                                [&](const VirtualValueExpr &other) {
                                  return exprEquals(result.operands.front(),
                                                    other);
                                });
        if (same)
          return result.operands.front();
      }
      break;
    default:
      break;
  }

  result.complete = std::all_of(
      result.operands.begin(), result.operands.end(),
      [](const VirtualValueExpr &operand) { return operand.complete; });
  return result;
}

static VirtualValueExpr specializeExprToFixpoint(
    VirtualValueExpr expr,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> *incoming_stack,
    const std::map<unsigned, VirtualValueExpr> *incoming_args,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    unsigned max_rounds = 4) {
  (void) max_rounds;
  annotateExprSlots(expr, slot_ids);
  annotateExprStackCells(expr, stack_cell_ids, slot_ids);
  auto specialized = specializeExpr(expr, incoming, incoming_stack, incoming_args);
  annotateExprSlots(specialized, slot_ids);
  annotateExprStackCells(specialized, stack_cell_ids, slot_ids);
  return specialized;
}

static void specializeFactStateToFixpoint(
    std::map<unsigned, VirtualValueExpr> &slot_facts,
    std::map<unsigned, VirtualValueExpr> &stack_facts,
    const std::map<unsigned, VirtualValueExpr> *argument_facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    unsigned max_rounds = 4) {
  (void) max_rounds;
  auto snapshot_slots = slot_facts;
  auto snapshot_stack = stack_facts;

  for (auto &[slot_id, value] : snapshot_slots) {
    (void) slot_id;
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
  }
  for (auto &[cell_id, value] : snapshot_stack) {
    (void) cell_id;
    annotateExprSlots(value, slot_ids);
    annotateExprStackCells(value, stack_cell_ids, slot_ids);
  }

  for (auto &[slot_id, value] : slot_facts) {
    value = specializeExprToFixpoint(value, snapshot_slots, &snapshot_stack,
                                     argument_facts, slot_ids,
                                     stack_cell_ids, /*max_rounds=*/1);
  }
  for (auto &[cell_id, value] : stack_facts) {
    value = specializeExprToFixpoint(value, snapshot_slots, &snapshot_stack,
                                     argument_facts, slot_ids,
                                     stack_cell_ids, /*max_rounds=*/1);
  }
}

static std::vector<VirtualSlotFact> computeOutgoingFacts(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_arg_map) {
  std::map<unsigned, VirtualValueExpr> outgoing = incoming_map;
  for (const auto &transfer : summary.state_transfers) {
    if (!transfer.target_slot.canonical_id.has_value())
      continue;
    outgoing[*transfer.target_slot.canonical_id] =
        specializeExpr(transfer.value, incoming_map, &incoming_stack_map,
                       &incoming_arg_map);
  }

  std::vector<VirtualSlotFact> facts;
  for (const auto &[slot_id, value] : outgoing)
    facts.push_back(VirtualSlotFact{slot_id, value});
  return facts;
}

static std::vector<VirtualStackFact> computeOutgoingStackFacts(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack_map,
    const std::map<unsigned, VirtualValueExpr> &incoming_arg_map) {
  std::map<unsigned, VirtualValueExpr> outgoing = incoming_stack_map;
  for (const auto &transfer : summary.stack_transfers) {
    if (!transfer.target_cell.canonical_id.has_value())
      continue;
    outgoing[*transfer.target_cell.canonical_id] =
        specializeExpr(transfer.value, incoming_map, &incoming_stack_map,
                       &incoming_arg_map);
  }

  std::vector<VirtualStackFact> facts;
  for (const auto &[cell_id, value] : outgoing)
    facts.push_back(VirtualStackFact{cell_id, value});
  return facts;
}

static std::map<SlotKey, unsigned> buildSlotIdMap(
    const VirtualMachineModel &model) {
  std::map<SlotKey, unsigned> slot_ids;
  for (const auto &slot : model.slots()) {
    slot_ids.emplace(SlotKey{slot.base_name, slot.offset, slot.width,
                             slot.from_argument, slot.from_alloca},
                     slot.id);
  }
  return slot_ids;
}

static std::map<unsigned, const VirtualStateSlotInfo *> buildSlotInfoMap(
    const VirtualMachineModel &model) {
  std::map<unsigned, const VirtualStateSlotInfo *> slot_info;
  for (const auto &slot : model.slots())
    slot_info.emplace(slot.id, &slot);
  return slot_info;
}

static std::map<StackCellKey, unsigned> buildStackCellIdMap(
    const VirtualMachineModel &model) {
  std::map<StackCellKey, unsigned> stack_cell_ids;
  for (const auto &cell : model.stackCells()) {
    stack_cell_ids.emplace(
        StackCellKey{SlotKey{cell.base_name, cell.base_offset, cell.base_width,
                             cell.base_from_argument, cell.base_from_alloca},
                     cell.cell_offset, cell.width},
        cell.id);
  }
  return stack_cell_ids;
}

static std::map<unsigned, const VirtualStackCellInfo *> buildStackCellInfoMap(
    const VirtualMachineModel &model) {
  std::map<unsigned, const VirtualStackCellInfo *> cell_info;
  for (const auto &cell : model.stackCells())
    cell_info.emplace(cell.id, &cell);
  return cell_info;
}

static llvm::DenseSet<unsigned> buildBooleanFlagSlotIds(
    llvm::Module &M, const VirtualMachineModel &model) {
  llvm::DenseSet<unsigned> boolean_slot_ids;
  StateFieldMap field_map(M);
  for (const auto &slot : model.slots()) {
    if (!slot.from_argument)
      continue;
    auto field = field_map.fieldAtOffset(static_cast<unsigned>(slot.offset));
    if (!field || field->category != StateFieldCategory::kFlag ||
        field->size != 1) {
      continue;
    }
    boolean_slot_ids.insert(slot.id);
  }
  return boolean_slot_ids;
}

static std::set<BooleanSlotExprKey> buildBooleanFlagExprKeys(
    llvm::Module &M, const VirtualMachineModel &model) {
  std::set<BooleanSlotExprKey> keys;
  StateFieldMap field_map(M);
  for (const auto &slot : model.slots()) {
    if (!slot.from_argument)
      continue;
    auto field = field_map.fieldAtOffset(static_cast<unsigned>(slot.offset));
    if (!field || field->category != StateFieldCategory::kFlag ||
        field->size != 1) {
      continue;
    }
    keys.emplace(slot.base_name, slot.offset, slot.from_argument,
                 slot.from_alloca);
  }
  return keys;
}

static std::optional<unsigned> parseArgumentBaseName(llvm::StringRef base_name) {
  if (!base_name.starts_with("arg"))
    return std::nullopt;
  unsigned arg_index = 0;
  if (base_name.drop_front(3).getAsInteger(10, arg_index))
    return std::nullopt;
  return arg_index;
}

static std::optional<unsigned> lookupSlotIdForSummary(
    const VirtualStateSlotSummary &summary,
    const std::map<SlotKey, unsigned> &slot_ids);

static std::optional<unsigned> lookupStackCellIdForSummary(
    const VirtualStackCellSummary &summary,
    const std::map<StackCellKey, unsigned> &stack_cell_ids);

static bool functionHasAllocaNamed(const llvm::Function &F,
                                   llvm::StringRef base_name) {
  for (const auto &BB : F) {
    for (const auto &I : BB) {
      const auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(&I);
      if (!alloca)
        continue;
      if (alloca->getName() == base_name)
        return true;
    }
  }
  return false;
}

static std::optional<unsigned> lookupMappedCallerSlotIdByPointerArgs(
    llvm::CallBase &call, llvm::StringRef callee_base_name,
    int64_t callee_offset, unsigned width,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl) {
  std::optional<unsigned> mapped_slot_id;
  for (unsigned arg_index = 0; arg_index < call.arg_size(); ++arg_index) {
    auto *actual_arg = call.getArgOperand(arg_index);
    if (!actual_arg->getType()->isPointerTy())
      continue;
    auto actual_slot = extractStateSlotSummary(actual_arg, width, dl);
    if (!actual_slot || !actual_slot->from_alloca ||
        actual_slot->base_name != callee_base_name) {
      continue;
    }

    VirtualStateSlotSummary mapped_slot = *actual_slot;
    mapped_slot.offset += callee_offset;
    mapped_slot.width = width;

    auto slot_id = lookupSlotIdForSummary(mapped_slot, slot_ids);
    if (!slot_id)
      continue;
    if (mapped_slot_id && *mapped_slot_id != *slot_id)
      return std::nullopt;
    mapped_slot_id = *slot_id;
  }
  return mapped_slot_id;
}

static std::optional<unsigned> lookupMappedCallerStackCellIdByPointerArgs(
    llvm::CallBase &call, llvm::StringRef callee_base_name,
    int64_t callee_base_offset, unsigned callee_base_width,
    int64_t callee_cell_offset, unsigned width,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  std::optional<unsigned> mapped_cell_id;
  for (unsigned arg_index = 0; arg_index < call.arg_size(); ++arg_index) {
    auto *actual_arg = call.getArgOperand(arg_index);
    if (!actual_arg->getType()->isPointerTy())
      continue;

    VirtualStackCellSummary mapped_cell;
    if (auto actual_slot =
            extractStateSlotSummary(actual_arg, callee_base_width, dl)) {
      if (!actual_slot->from_alloca ||
          actual_slot->base_name != callee_base_name) {
        continue;
      }
      mapped_cell.base_name = actual_slot->base_name;
      mapped_cell.base_offset = actual_slot->offset + callee_base_offset;
      mapped_cell.base_width = actual_slot->width;
      mapped_cell.base_from_argument = actual_slot->from_argument;
      mapped_cell.base_from_alloca = actual_slot->from_alloca;
      mapped_cell.offset = callee_cell_offset;
      mapped_cell.width = width;
    } else if (auto actual_cell =
                   extractStackCellSummaryFromExpr(summarizeValueExpr(actual_arg, dl),
                                                  width)) {
      if (!actual_cell->base_from_alloca ||
          actual_cell->base_name != callee_base_name ||
          actual_cell->base_offset != callee_base_offset) {
        continue;
      }
      mapped_cell = *actual_cell;
      mapped_cell.offset += callee_cell_offset;
      mapped_cell.width = width;
    } else {
      continue;
    }

    auto cell_id = lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
    if (!cell_id)
      continue;
    if (mapped_cell_id && *mapped_cell_id != *cell_id)
      return std::nullopt;
    mapped_cell_id = *cell_id;
  }
  return mapped_cell_id;
}

static std::optional<int64_t> stackBaseDeltaForExpr(const VirtualValueExpr &expr,
                                                    unsigned slot_id) {
  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id == slot_id)
    return 0;

  if ((expr.kind == VirtualExprKind::kAdd || expr.kind == VirtualExprKind::kSub) &&
      expr.operands.size() == 2) {
    if (auto nested = stackBaseDeltaForExpr(expr.operands[0], slot_id);
        nested && expr.operands[1].constant.has_value()) {
      int64_t delta = static_cast<int64_t>(*expr.operands[1].constant);
      if (expr.kind == VirtualExprKind::kSub)
        delta = -delta;
      return *nested + delta;
    }
    if (expr.kind == VirtualExprKind::kAdd &&
        expr.operands[0].constant.has_value()) {
      if (auto nested = stackBaseDeltaForExpr(expr.operands[1], slot_id))
        return *nested + static_cast<int64_t>(*expr.operands[0].constant);
    }
  }

  return std::nullopt;
}

static std::optional<int64_t> findStackBaseDeltaForSlot(
    const std::map<unsigned, VirtualValueExpr> &slot_facts, unsigned slot_id) {
  std::optional<int64_t> found_delta;

  auto consider_delta = [&](const VirtualValueExpr &value) {
    auto delta = stackBaseDeltaForExpr(value, slot_id);
    if (!delta)
      return true;
    if (!found_delta) {
      found_delta = *delta;
      return true;
    }
    return *found_delta == *delta;
  };

  if (auto it = slot_facts.find(slot_id); it != slot_facts.end()) {
    if (!consider_delta(it->second))
      return std::nullopt;
  }

  for (const auto &[fact_slot_id, value] : slot_facts) {
    if (fact_slot_id == slot_id)
      continue;
    if (!consider_delta(value))
      return std::nullopt;
  }

  return found_delta;
}

static std::map<unsigned, VirtualValueExpr> rebaseOutgoingStackFacts(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    const std::map<unsigned, VirtualValueExpr> &outgoing_stack) {
  std::map<unsigned, int64_t> base_deltas;
  for (const auto &slot : model.slots()) {
    if (auto delta = findStackBaseDeltaForSlot(outgoing_slots, slot.id))
      base_deltas.emplace(slot.id, *delta);
  }
  if (base_deltas.empty())
    return outgoing_stack;

  std::map<std::pair<unsigned, int64_t>, unsigned> cell_by_base_and_offset;
  std::map<unsigned, const VirtualStackCellInfo *> cell_info;
  for (const auto &cell : model.stackCells()) {
    cell_by_base_and_offset.emplace(
        std::make_pair(cell.base_slot_id, cell.cell_offset), cell.id);
    cell_info.emplace(cell.id, &cell);
  }

  std::map<unsigned, VirtualValueExpr> rebased;
  for (const auto &[cell_id, value] : outgoing_stack) {
    unsigned mapped_cell_id = cell_id;
    auto info_it = cell_info.find(cell_id);
    if (info_it != cell_info.end()) {
      const auto *info = info_it->second;
      auto delta_it = base_deltas.find(info->base_slot_id);
      if (delta_it != base_deltas.end()) {
        auto target_it = cell_by_base_and_offset.find(
            std::make_pair(info->base_slot_id,
                           info->cell_offset - delta_it->second));
        if (target_it != cell_by_base_and_offset.end())
          mapped_cell_id = target_it->second;
      }
    }

    auto existing = rebased.find(mapped_cell_id);
    if (existing == rebased.end()) {
      rebased.emplace(mapped_cell_id, value);
      continue;
    }
    auto merged = mergeIncomingExpr(existing->second, value);
    if (merged.has_value()) {
      existing->second = std::move(*merged);
    } else {
      existing->second = unknownExpr(existing->second.bit_width
                                         ? existing->second.bit_width
                                         : value.bit_width);
    }
  }

  return rebased;
}

static bool mergeFactIntoMap(std::map<unsigned, VirtualValueExpr> &dst,
                             unsigned id, const VirtualValueExpr &value) {
  auto existing = dst.find(id);
  if (existing == dst.end()) {
    dst.emplace(id, value);
    return true;
  }
  if (exprEquals(existing->second, value))
    return false;

  auto merged = mergeIncomingExpr(existing->second, value);
  if (merged.has_value()) {
    if (!exprEquals(existing->second, *merged)) {
      existing->second = std::move(*merged);
      return true;
    }
    return false;
  }

  auto unknown = unknownExpr(existing->second.bit_width
                                 ? existing->second.bit_width
                                 : value.bit_width);
  if (!exprEquals(existing->second, unknown)) {
    existing->second = std::move(unknown);
    return true;
  }
  return false;
}

static llvm::SmallDenseSet<unsigned, 16> rebaseWrittenStackCellIds(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    llvm::ArrayRef<unsigned> written_stack_cell_ids) {
  std::map<unsigned, int64_t> base_deltas;
  for (const auto &slot : model.slots()) {
    if (auto delta = findStackBaseDeltaForSlot(outgoing_slots, slot.id))
      base_deltas.emplace(slot.id, *delta);
  }
  if (base_deltas.empty()) {
    return llvm::SmallDenseSet<unsigned, 16>(written_stack_cell_ids.begin(),
                                             written_stack_cell_ids.end());
  }

  std::map<std::pair<unsigned, int64_t>, unsigned> cell_by_base_and_offset;
  std::map<unsigned, const VirtualStackCellInfo *> cell_info;
  for (const auto &cell : model.stackCells()) {
    cell_by_base_and_offset.emplace(
        std::make_pair(cell.base_slot_id, cell.cell_offset), cell.id);
    cell_info.emplace(cell.id, &cell);
  }

  llvm::SmallDenseSet<unsigned, 16> rebased_ids;
  for (unsigned cell_id : written_stack_cell_ids) {
    unsigned mapped_cell_id = cell_id;
    auto info_it = cell_info.find(cell_id);
    if (info_it != cell_info.end()) {
      const auto *info = info_it->second;
      auto delta_it = base_deltas.find(info->base_slot_id);
      if (delta_it != base_deltas.end()) {
        auto target_it = cell_by_base_and_offset.find(
            std::make_pair(info->base_slot_id,
                           info->cell_offset - delta_it->second));
        if (target_it != cell_by_base_and_offset.end())
          mapped_cell_id = target_it->second;
      }
    }
    rebased_ids.insert(mapped_cell_id);
  }

  return rebased_ids;
}

static unsigned rebaseSingleStackCellId(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    unsigned cell_id) {
  auto rebased = rebaseWrittenStackCellIds(model, outgoing_slots, {cell_id});
  return rebased.empty() ? cell_id : *rebased.begin();
}

struct CallsiteLocalizedOutgoingFacts {
  std::map<unsigned, VirtualValueExpr> outgoing_slots;
  std::map<unsigned, VirtualValueExpr> outgoing_stack;
};

static std::vector<VirtualSlotFact> slotFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts);

static std::vector<VirtualStackFact> stackFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts);

static constexpr unsigned kMaxCallsiteLocalizationDepth = 4;
static constexpr unsigned kMaxLocalizedDirectCallees = 8;
static constexpr unsigned kMaxLocalizedLeafHelperInstructions = 32;
static constexpr unsigned kMaxLocalizedSingleBlockHandlerInstructions = 96;

static std::optional<llvm::SmallVector<llvm::BasicBlock *, 4>>
collectLocalizedReplayBlocks(llvm::Function &F,
                             const VirtualHandlerSummary &summary) {
  auto log_skip = [&](llvm::StringRef reason) {
    if (!vmModelLocalReplayDebugEnabled())
      return;
    unsigned total_instrs = 0;
    for (const auto &BB : F)
      total_instrs += static_cast<unsigned>(BB.size());
    vmModelLocalReplayDebugLog("skip-local-replay fn=" + F.getName().str() +
                               " reason=" + reason.str() + " blocks=" +
                               std::to_string(F.size()) + " instrs=" +
                               std::to_string(total_instrs));
  };

  if (F.empty()) {
    log_skip("empty");
    return std::nullopt;
  }
  if (!summary.callsites.empty()) {
    log_skip("callsites");
    return std::nullopt;
  }
  if (!summary.dispatches.empty()) {
    log_skip("dispatches");
    return std::nullopt;
  }
  if (summary.direct_callees.size() > kMaxLocalizedDirectCallees) {
    log_skip("too-many-direct-callees");
    return std::nullopt;
  }

  unsigned instruction_budget = summary.direct_callees.empty()
                                    ? kMaxLocalizedLeafHelperInstructions
                                    : kMaxLocalizedSingleBlockHandlerInstructions;
  unsigned instruction_count = 0;
  llvm::SmallVector<llvm::BasicBlock *, 4> blocks;
  llvm::SmallPtrSet<const llvm::BasicBlock *, 4> seen;
  auto *block = &F.getEntryBlock();

  while (block) {
    if (!seen.insert(block).second) {
      log_skip("cycle");
      return std::nullopt;
    }
    instruction_count += static_cast<unsigned>(block->size());
    if (instruction_count > instruction_budget) {
      log_skip("instruction-budget");
      return std::nullopt;
    }
    blocks.push_back(block);

    auto *term = block->getTerminator();
    if (!term) {
      log_skip("no-terminator");
      return std::nullopt;
    }
    if (llvm::isa<llvm::ReturnInst>(term) || llvm::isa<llvm::UnreachableInst>(term))
      break;

    auto *br = llvm::dyn_cast<llvm::BranchInst>(term);
    if (!br || !br->isUnconditional()) {
      log_skip("nonlinear-terminator");
      return std::nullopt;
    }

    auto *next = br->getSuccessor(0);
    if (!next || !next->hasNPredecessors(1)) {
      log_skip("multi-predecessor");
      return std::nullopt;
    }
    block = next;
  }

  if (seen.size() != F.size()) {
    log_skip("unreached-blocks");
    return std::nullopt;
  }
  return blocks;
}

static std::optional<VirtualStateSlotSummary> extractStateSlotSummaryFromExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info);

static std::optional<unsigned> lookupMappedCallerSlotId(
    llvm::CallBase &call, const VirtualStateSlotInfo &callee_slot,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl);

static std::optional<unsigned> lookupMappedCallerStackCellId(
    llvm::CallBase &call, const VirtualStackCellInfo &callee_cell,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl);

struct ResolvedCallSiteInfo {
  VirtualValueExpr target_expr;
  VirtualDispatchResolutionSource target_source =
      VirtualDispatchResolutionSource::kUnknown;
  std::optional<uint64_t> target_pc;
  std::optional<uint64_t> continuation_pc;
};

struct LocalCallSiteState {
  std::map<unsigned, VirtualValueExpr> slot_facts;
  std::map<unsigned, VirtualValueExpr> stack_facts;
};

static VirtualValueExpr stateSlotExpr(const VirtualStateSlotSummary &slot) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kStateSlot;
  expr.bit_width = slot.width ? slot.width * 8u : 0u;
  expr.complete = true;
  expr.state_base_name = slot.base_name;
  expr.state_offset = slot.offset;
  expr.slot_id = slot.canonical_id;
  return expr;
}

static VirtualValueExpr stackCellExpr(const VirtualStackCellSummary &cell) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kStackCell;
  expr.bit_width = cell.width ? cell.width * 8u : 0u;
  expr.complete = true;
  expr.state_base_name = cell.base_name;
  expr.state_offset = cell.base_offset;
  expr.stack_offset = cell.offset;
  expr.slot_id = cell.canonical_base_slot_id;
  expr.stack_cell_id = cell.canonical_id;
  return expr;
}

static std::map<unsigned, VirtualValueExpr> buildSpecializedCallArgumentMap(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);

static ResolvedCallSiteInfo resolveCallSiteInfo(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);

static const VirtualHandlerSummary *lookupHandlerByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va);

static LocalCallSiteState computeLocalFactsBeforeCall(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &base_slot_facts,
    const std::map<unsigned, VirtualValueExpr> &base_stack_facts,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);

static std::optional<CallsiteLocalizedOutgoingFacts>
computeResolvedCallTargetOutgoingFacts(
    llvm::CallBase &call, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    const ResolvedCallSiteInfo &callsite, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);

static std::optional<CallsiteLocalizedOutgoingFacts>
computeEntryPreludeCallOutgoingFacts(
    llvm::Module &M, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    uint64_t continuation_pc, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);

static void applyLocalizedCallsiteReturnEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const VirtualHandlerSummary &caller_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    unsigned depth, llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);

static VirtualValueExpr remapCalleeExprToCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl);

static std::optional<VirtualValueExpr> normalizeImportedExprForCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);

static std::optional<VirtualValueExpr> normalizeLocalizedExprForCaller(
    const VirtualValueExpr &expr, const llvm::Function &caller_fn,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);

static std::optional<CallsiteLocalizedOutgoingFacts>
computeCallsiteLocalizedOutgoingFacts(
    llvm::CallBase &call, const VirtualMachineModel &model,
    const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);

static bool applySingleDirectCalleeEffects(
    llvm::Function &caller_fn, llvm::CallBase &call,
    const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const llvm::DataLayout &dl, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  auto *callee = call.getCalledFunction();
  if (!callee)
    return false;

  auto callee_it = handler_index.find(callee->getName().str());
  if (callee_it == handler_index.end())
    return false;

  const auto &callee_summary = model.handlers()[callee_it->second];
  const auto specialized_call_args = buildSpecializedCallArgumentMap(
      call, dl, slot_ids, stack_cell_ids, caller_outgoing,
      caller_outgoing_stack, caller_argument_map);
  llvm::SmallDenseSet<unsigned, 16> written_slots(
      callee_summary.written_slot_ids.begin(),
      callee_summary.written_slot_ids.end());
  auto localized_outgoing = computeCallsiteLocalizedOutgoingFacts(
      call, model, callee_summary, slot_info, stack_cell_info, slot_ids,
      stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
      caller_outgoing, caller_outgoing_stack, caller_argument_map, depth + 1,
      visiting);
  const auto &callee_outgoing_map =
      localized_outgoing ? localized_outgoing->outgoing_slots
                         : outgoing_maps[callee_it->second];
  const auto &callee_outgoing_stack_map =
      localized_outgoing ? localized_outgoing->outgoing_stack
                         : outgoing_stack_maps[callee_it->second];
  if (localized_outgoing) {
    vmModelImportDebugLog("callsite-local effects call=" +
                          callee->getName().str());
  }
  llvm::SmallDenseSet<unsigned, 16> written_stack_cells;
  if (localized_outgoing) {
    for (const auto &[cell_id, value] : callee_outgoing_stack_map) {
      (void) value;
      written_stack_cells.insert(cell_id);
    }
  } else {
    written_stack_cells = rebaseWrittenStackCellIds(
        model, callee_outgoing_map, callee_summary.written_stack_cell_ids);
  }

  for (const auto &[callee_slot_id, callee_value] : callee_outgoing_map) {
    if (!written_slots.empty() && !written_slots.count(callee_slot_id))
      continue;
    auto slot_info_it = slot_info.find(callee_slot_id);
    if (slot_info_it == slot_info.end())
      continue;
    std::optional<unsigned> mapped_slot_id;
    if (auto arg_index = parseArgumentBaseName(slot_info_it->second->base_name);
        !mapped_slot_id && arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStateSlotSummary mapped_slot = *actual_slot;
          mapped_slot.offset += slot_info_it->second->offset;
          mapped_slot.width = slot_info_it->second->width;
          mapped_slot_id = lookupSlotIdForSummary(mapped_slot, slot_ids);
        }
      }
    }
    if (!mapped_slot_id) {
      mapped_slot_id =
          lookupMappedCallerSlotId(call, *slot_info_it->second, slot_ids, dl);
    }
    if (!mapped_slot_id)
      continue;

    auto remapped =
        remapCalleeExprToCaller(callee_value, call, slot_info, stack_cell_info,
                                slot_ids, stack_cell_ids, dl);
    vmModelImportDebugLog("slot-import before call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(callee_value) +
                          " remapped=" + renderVirtualValueExpr(remapped));
    auto specialized =
        localized_outgoing
            ? normalizeLocalizedExprForCaller(
                  callee_value, caller_fn, slot_ids, stack_cell_ids,
                  caller_outgoing, caller_outgoing_stack, caller_argument_map)
            : normalizeImportedExprForCaller(
                  callee_value, call, slot_info, stack_cell_info, slot_ids,
                  stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
                  caller_argument_map);
    if (localized_outgoing &&
        (!specialized.has_value() ||
         (specialized.has_value() &&
          (isUnknownLikeExpr(*specialized) ||
           !isBoundedStateProvenanceExpr(*specialized))))) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
              caller_argument_map)) {
        specialized = std::move(remapped);
      }
    }
    if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
        !isBoundedStateProvenanceExpr(*specialized)) {
      if (vmModelImportDebugEnabled()) {
        std::string reason = !specialized.has_value()
                                 ? "no-specialized"
                                 : (isUnknownLikeExpr(*specialized) ? "unknown"
                                                                    : "unbounded");
        vmModelImportDebugLog("slot-import skip call=" +
                              callee->getName().str() + " reason=" + reason +
                              " expr=" + renderVirtualValueExpr(callee_value) +
                              " specialized=" +
                              (specialized.has_value()
                                   ? renderVirtualValueExpr(*specialized)
                                   : std::string("<none>")));
      }
      continue;
    }
    auto existing = caller_outgoing.find(*mapped_slot_id);
    if (existing != caller_outgoing.end() &&
        !exprEquals(existing->second, *specialized) &&
        isIdentitySlotExpr(*specialized, *mapped_slot_id)) {
      continue;
    }
    vmModelImportDebugLog("slot-import after call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(*specialized) +
                          " mapped_slot=" +
                          std::to_string(*mapped_slot_id) + "(" +
                          slot_info.at(*mapped_slot_id)->base_name + "+" +
                          std::to_string(slot_info.at(*mapped_slot_id)->offset) +
                          ")");
    caller_outgoing[*mapped_slot_id] = std::move(*specialized);
  }

  for (const auto &[callee_cell_id, callee_value] : callee_outgoing_stack_map) {
    if (!written_stack_cells.empty() &&
        !written_stack_cells.count(callee_cell_id)) {
      continue;
    }
    auto cell_info_it = stack_cell_info.find(callee_cell_id);
    if (cell_info_it == stack_cell_info.end())
      continue;
    std::optional<unsigned> mapped_cell_id;
    if (auto arg_index = parseArgumentBaseName(cell_info_it->second->base_name);
        !mapped_cell_id && arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStackCellSummary mapped_cell;
          mapped_cell.base_name = actual_slot->base_name;
          mapped_cell.base_offset =
              actual_slot->offset + cell_info_it->second->base_offset;
          mapped_cell.base_width = actual_slot->width;
          mapped_cell.base_from_argument = actual_slot->from_argument;
          mapped_cell.base_from_alloca = actual_slot->from_alloca;
          mapped_cell.offset = cell_info_it->second->cell_offset;
          mapped_cell.width = cell_info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        } else if (auto actual_cell = extractStackCellSummaryFromExpr(
                       expr_it->second, cell_info_it->second->width)) {
          VirtualStackCellSummary mapped_cell = *actual_cell;
          mapped_cell.offset += cell_info_it->second->cell_offset;
          mapped_cell.width = cell_info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        }
      }
    }
    if (!mapped_cell_id) {
      mapped_cell_id = lookupMappedCallerStackCellId(
          call, *cell_info_it->second, slot_ids, stack_cell_ids, dl);
    }
    if (!mapped_cell_id)
      continue;

    auto remapped =
        remapCalleeExprToCaller(callee_value, call, slot_info, stack_cell_info,
                                slot_ids, stack_cell_ids, dl);
    vmModelImportDebugLog("stack-import before call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(callee_value) +
                          " remapped=" + renderVirtualValueExpr(remapped));
    auto specialized =
        localized_outgoing
            ? normalizeLocalizedExprForCaller(
                  callee_value, caller_fn, slot_ids, stack_cell_ids,
                  caller_outgoing, caller_outgoing_stack, caller_argument_map)
            : normalizeImportedExprForCaller(
                  callee_value, call, slot_info, stack_cell_info, slot_ids,
                  stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
                  caller_argument_map);
    if (localized_outgoing &&
        (!specialized.has_value() ||
         (specialized.has_value() &&
          (isUnknownLikeExpr(*specialized) ||
           !isBoundedStateProvenanceExpr(*specialized))))) {
      if (auto remapped = normalizeImportedExprForCaller(
              callee_value, call, slot_info, stack_cell_info, slot_ids,
              stack_cell_ids, dl, caller_outgoing, caller_outgoing_stack,
              caller_argument_map)) {
        specialized = std::move(remapped);
      }
    }
    if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
        !isBoundedStateProvenanceExpr(*specialized)) {
      continue;
    }
    auto existing = caller_outgoing_stack.find(*mapped_cell_id);
    if (existing != caller_outgoing_stack.end() &&
        !exprEquals(existing->second, *specialized) &&
        isIdentityStackCellExpr(*specialized, *mapped_cell_id)) {
      continue;
    }
    vmModelImportDebugLog("stack-import after call=" + callee->getName().str() +
                          " expr=" + renderVirtualValueExpr(*specialized) +
                          " mapped_cell=" +
                          std::to_string(*mapped_cell_id) + "(" +
                          stack_cell_info.at(*mapped_cell_id)->base_name + "+" +
                          std::to_string(
                              stack_cell_info.at(*mapped_cell_id)->base_offset) +
                          "," +
                          std::to_string(
                              stack_cell_info.at(*mapped_cell_id)->cell_offset) +
                          ")");
    caller_outgoing_stack[*mapped_cell_id] = std::move(*specialized);
  }

  return true;
}

static void applyDirectCalleeEffectsImpl(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const llvm::DataLayout &dl, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  for (auto &BB : caller_fn) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;
      if (applySingleDirectCalleeEffects(
              caller_fn, *call, model, handler_index, outgoing_maps,
              outgoing_stack_maps, caller_argument_map, caller_outgoing,
              caller_outgoing_stack, slot_ids, slot_info, stack_cell_ids,
              stack_cell_info, dl, depth, visiting)) {
        continue;
      }

      if (!isCallSiteHelper(*callee))
        continue;

      auto local_state = computeLocalFactsBeforeCall(
          *call, dl, slot_ids, stack_cell_ids,
          /*base_slot_facts=*/{}, /*base_stack_facts=*/{}, caller_argument_map);
      auto callsite = resolveCallSiteInfo(
          *call, dl, slot_ids, stack_cell_ids, local_state.slot_facts,
          local_state.stack_facts, caller_argument_map);
      if (!callsite.target_pc.has_value())
        continue;

      const auto *target_summary = lookupHandlerByEntryVA(model, *callsite.target_pc);
      if (!target_summary)
        continue;

      auto localized_outgoing = computeResolvedCallTargetOutgoingFacts(
          *call, model, *target_summary, slot_info, stack_cell_info, slot_ids,
          stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
          caller_outgoing, caller_outgoing_stack, caller_argument_map, callsite,
          depth + 1, visiting);
      if (!localized_outgoing)
        continue;

      vmModelImportDebugLog("call-root effects call=" + callee->getName().str() +
                            " target=0x" +
                            llvm::utohexstr(*callsite.target_pc) + " fn=" +
                            target_summary->function_name);

      llvm::SmallDenseSet<unsigned, 16> written_slots(
          target_summary->written_slot_ids.begin(),
          target_summary->written_slot_ids.end());
      llvm::SmallDenseSet<unsigned, 16> written_stack_cells;
      for (const auto &[cell_id, value] : localized_outgoing->outgoing_stack) {
        (void) value;
        written_stack_cells.insert(cell_id);
      }

      for (const auto &[slot_id, value] : localized_outgoing->outgoing_slots) {
        if (!written_slots.empty() && !written_slots.count(slot_id))
          continue;
        auto specialized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, caller_argument_map);
        if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
            !isBoundedStateProvenanceExpr(*specialized)) {
          continue;
        }
        auto existing = caller_outgoing.find(slot_id);
        if (existing != caller_outgoing.end() &&
            !exprEquals(existing->second, *specialized) &&
            isIdentitySlotExpr(*specialized, slot_id)) {
          continue;
        }
        vmModelImportDebugLog("call-root slot-import after call=" +
                              callee->getName().str() + " expr=" +
                              renderVirtualValueExpr(*specialized));
        caller_outgoing[slot_id] = std::move(*specialized);
      }

      for (const auto &[cell_id, value] : localized_outgoing->outgoing_stack) {
        if (!written_stack_cells.empty() && !written_stack_cells.count(cell_id))
          continue;
        auto specialized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, caller_argument_map);
        if (!specialized.has_value() || isUnknownLikeExpr(*specialized) ||
            !isBoundedStateProvenanceExpr(*specialized)) {
          continue;
        }
        auto existing = caller_outgoing_stack.find(cell_id);
        if (existing != caller_outgoing_stack.end() &&
            !exprEquals(existing->second, *specialized) &&
            isIdentityStackCellExpr(*specialized, cell_id)) {
          continue;
        }
        vmModelImportDebugLog("call-root stack-import after call=" +
                              callee->getName().str() + " expr=" +
                              renderVirtualValueExpr(*specialized) +
                              " cell=" + std::to_string(cell_id));
        caller_outgoing_stack[cell_id] = std::move(*specialized);
      }

    }
  }
}

static bool canRecursivelyLocalizeCallsiteSummary(
    const VirtualHandlerSummary &summary, unsigned depth) {
  if (depth > kMaxCallsiteLocalizationDepth)
    return false;
  if (!summary.dispatches.empty())
    return false;
  return summary.direct_callees.size() <= kMaxLocalizedDirectCallees;
}

static std::optional<unsigned> lookupNativeStackPointerOffset(llvm::Module &M) {
  StateFieldMap field_map(M);
  for (const char *sp_name : {"RSP", "SP", "sp"}) {
    if (auto field = field_map.fieldByName(sp_name))
      return field->offset;
  }
  return std::nullopt;
}

static std::optional<uint64_t> inferLiftedCallContinuationPc(llvm::CallBase &call) {
  llvm::Value *continuation_input = &call;
  llvm::CallBase *intermediate_lifted_call = nullptr;

  for (auto *I = call.getNextNode(); I; I = I->getNextNode()) {
    if (auto *next_call = llvm::dyn_cast<llvm::CallBase>(I)) {
      auto *next_callee = next_call->getCalledFunction();
      if (!next_callee || !hasLiftedSignature(*next_callee))
        continue;
      auto *next_call_inst = llvm::dyn_cast<llvm::CallInst>(next_call);
      if (next_call_inst &&
          next_call_inst->getTailCallKind() == llvm::CallInst::TCK_MustTail &&
          next_call->arg_size() >= 3 &&
          next_call->getArgOperand(2) == continuation_input) {
        auto *pc = llvm::dyn_cast<llvm::ConstantInt>(next_call->getArgOperand(1));
        if (!pc)
          return std::nullopt;
        return pc->getZExtValue();
      }

      if (!intermediate_lifted_call) {
        intermediate_lifted_call = next_call;
        continuation_input = intermediate_lifted_call;
      }
    }

    if (I->isTerminator())
      break;
  }

  return std::nullopt;
}

static const VirtualHandlerSummary *lookupHandlerByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va) {
  for (const auto &handler : model.handlers()) {
    if (handler.entry_va.has_value() && *handler.entry_va == entry_va)
      return &handler;
  }
  return nullptr;
}

static bool isTargetMapped(const BinaryMemoryMap &binary_memory,
                           uint64_t target_pc) {
  if (target_pc == 0)
    return false;
  uint8_t byte = 0;
  return binary_memory.read(target_pc, &byte, 1);
}

static bool isTargetExecutable(const BinaryMemoryMap &binary_memory,
                               uint64_t target_pc) {
  if (target_pc == 0)
    return false;
  return binary_memory.isExecutable(target_pc, 1);
}

static TargetArch targetArchForModule(llvm::Module &M) {
  TargetArch arch = TargetArch::kX86_64;

  if (auto *md = M.getModuleFlag("omill.target_arch")) {
    if (auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(md))
      arch = static_cast<TargetArch>(ci->getZExtValue());
  }
  return arch;
}

static std::optional<bool> isTargetDecodableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch arch) {
  if (!isTargetExecutable(binary_memory, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      if (target_pc & 0x3)
        return false;
      uint8_t buf[4] = {};
      return binary_memory.read(target_pc, buf, sizeof(buf));
    }
    case TargetArch::kX86_64:
    default:
      return canDecodeX86InstructionAt(binary_memory, target_pc);
  }
}

static uint64_t nearbyEntrySearchWindow(TargetArch arch) {
  switch (arch) {
    case TargetArch::kAArch64:
      return 4;
    case TargetArch::kX86_64:
    default:
      return 15;
  }
}

static const VirtualHandlerSummary *findNearbyLiftedHandlerEntry(
    const VirtualMachineModel &model, uint64_t target_pc, TargetArch arch) {
  const auto window = nearbyEntrySearchWindow(arch);
  const VirtualHandlerSummary *best = nullptr;
  for (const auto &handler : model.handlers()) {
    if (!handler.entry_va.has_value())
      continue;
    const auto entry_va = *handler.entry_va;
    if (entry_va >= target_pc)
      continue;
    if ((target_pc - entry_va) > window)
      continue;
    if (!best || *best->entry_va < entry_va)
      best = &handler;
  }
  return best;
}

template <typename HandlerPtr>
static HandlerPtr findNearbyLiftedHandlerEntry(
    const std::map<uint64_t, HandlerPtr> &handler_by_pc, uint64_t target_pc,
    TargetArch arch) {
  const auto window = nearbyEntrySearchWindow(arch);
  auto it = handler_by_pc.lower_bound(target_pc);
  while (it != handler_by_pc.begin()) {
    --it;
    if ((target_pc - it->first) > window)
      break;
    return it->second;
  }
  return nullptr;
}

static std::optional<uint64_t> findNearbyExecutableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc,
    TargetArch arch) {
  if (!isTargetExecutable(binary_memory, target_pc))
    return std::nullopt;

  switch (arch) {
    case TargetArch::kAArch64: {
      auto aligned = target_pc & ~uint64_t(0x3);
      if (aligned == target_pc)
        return std::nullopt;
      auto decodable = isTargetDecodableEntry(binary_memory, aligned, arch);
      if (decodable.has_value() && *decodable)
        return aligned;
      return std::nullopt;
    }
    case TargetArch::kX86_64:
    default: {
      const uint64_t kWindow = nearbyEntrySearchWindow(arch);
      uint64_t start = (target_pc > kWindow) ? (target_pc - kWindow) : 1;
      for (uint64_t candidate = target_pc; candidate > start; --candidate) {
        uint64_t pc = candidate - 1;
        if (!isTargetExecutable(binary_memory, pc))
          continue;
        auto decodable = isTargetDecodableEntry(binary_memory, pc, arch);
        if (decodable.has_value() && *decodable)
          return pc;
      }
      return std::nullopt;
    }
  }
}

static bool isCallerStateArgumentExpr(const VirtualValueExpr &expr) {
  return expr.kind == VirtualExprKind::kArgument &&
         expr.argument_index.has_value() && *expr.argument_index == 0;
}

static LocalCallSiteState computeLocalFactsBeforeCall(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &base_slot_facts,
    const std::map<unsigned, VirtualValueExpr> &base_stack_facts,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  LocalCallSiteState state{base_slot_facts, base_stack_facts};
  auto *block = call.getParent();
  if (!block)
    return state;

  auto record_value = [&](llvm::Value *value) {
    auto expr = summarizeValueExpr(value, dl);
    return specializeExprToFixpoint(expr, state.slot_facts, &state.stack_facts,
                                    &caller_argument_map, slot_ids,
                                    stack_cell_ids);
  };

  for (auto &I : *block) {
    if (&I == &call)
      break;

    if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto width = dl.getTypeStoreSize(store->getValueOperand()->getType());
      if (width.isScalable())
        continue;
      if (auto slot = extractStateSlotSummary(store->getPointerOperand(),
                                              width.getFixedValue(), dl)) {
        auto slot_id = lookupSlotIdForSummary(*slot, slot_ids);
        if (!slot_id)
          continue;
        state.slot_facts[*slot_id] = record_value(store->getValueOperand());
        continue;
      }
      auto pointer_expr = summarizeValueExpr(store->getPointerOperand(), dl);
      if (auto cell = extractStackCellSummaryFromExpr(pointer_expr,
                                                      width.getFixedValue())) {
        auto cell_id = lookupStackCellIdForSummary(*cell, stack_cell_ids);
        if (!cell_id)
          continue;
        state.stack_facts[*cell_id] = record_value(store->getValueOperand());
      }
      continue;
    }

    auto *cb = llvm::dyn_cast<llvm::CallBase>(&I);
    if (!cb)
      continue;
    auto *callee = cb->getCalledFunction();
    if (!callee || !isRemillWriteMemoryIntrinsic(*callee) || cb->arg_size() < 3)
      continue;

    unsigned width_bits = remillMemoryBitWidth(callee->getName()).value_or(0);
    unsigned width_bytes = width_bits / 8;
    auto address_expr = summarizeValueExpr(cb->getArgOperand(1), dl);
    if (auto cell = extractStackCellSummaryFromExpr(address_expr, width_bytes)) {
      auto cell_id = lookupStackCellIdForSummary(*cell, stack_cell_ids);
      if (!cell_id)
        continue;
      state.stack_facts[*cell_id] = record_value(cb->getArgOperand(2));
    }
  }

  specializeFactStateToFixpoint(state.slot_facts, state.stack_facts,
                                &caller_argument_map, slot_ids,
                                stack_cell_ids);
  return state;
}

static VirtualValueExpr summarizeSpecializedCallArg(
    llvm::CallBase &call, unsigned arg_index, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  if (arg_index >= call.arg_size())
    return VirtualValueExpr{};
  auto expr = summarizeValueExpr(call.getArgOperand(arg_index), dl);
  return specializeExprToFixpoint(expr, caller_outgoing, &caller_outgoing_stack,
                                  &caller_argument_map, slot_ids,
                                  stack_cell_ids);
}

static std::map<unsigned, VirtualValueExpr> buildSpecializedCallArgumentMap(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  std::map<unsigned, VirtualValueExpr> specialized_args;
  for (unsigned arg_index = 0; arg_index < call.arg_size(); ++arg_index) {
    specialized_args.emplace(
        arg_index,
        summarizeSpecializedCallArg(call, arg_index, dl, slot_ids,
                                    stack_cell_ids, caller_outgoing,
                                    caller_outgoing_stack, caller_argument_map));
  }
  return specialized_args;
}

static bool canComputeLocalizedSingleBlockOutgoingFacts(
    const llvm::Function &F, const VirtualHandlerSummary &summary) {
  auto &mutable_function = const_cast<llvm::Function &>(F);
  return collectLocalizedReplayBlocks(mutable_function, summary).has_value();
}

static std::optional<CallsiteLocalizedOutgoingFacts>
computeLocalizedSingleBlockOutgoingFacts(
    llvm::Function &F, const VirtualMachineModel &model,
    const VirtualHandlerSummary &summary,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &incoming_slots,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &incoming_args,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    unsigned depth, llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    llvm::CallBase *localizing_call = nullptr,
    const std::map<unsigned, VirtualValueExpr> *caller_stack_facts = nullptr,
    const std::map<unsigned, VirtualValueExpr> *caller_slot_facts = nullptr) {
  (void) summary;
  (void) localizing_call;
  (void) caller_stack_facts;
  (void) caller_slot_facts;
  auto replay_blocks = collectLocalizedReplayBlocks(F, summary);
  if (!replay_blocks)
    return std::nullopt;

  const auto &dl = F.getParent()->getDataLayout();
  const auto slot_info = buildSlotInfoMap(model);
  const auto stack_cell_info = buildStackCellInfoMap(model);
  struct LocalLeafReplayState {
    std::map<unsigned, VirtualValueExpr> slot_facts;
    std::map<unsigned, VirtualValueExpr> stack_facts;
    llvm::DenseMap<const llvm::Value *, VirtualValueExpr> value_facts;
  };

  LocalLeafReplayState state;
  state.slot_facts = incoming_slots;
  state.stack_facts = incoming_stack;
  auto normalize_expr = [&](VirtualValueExpr expr,
                            unsigned fallback_bits = 0u) {
    if (!expr.bit_width)
      expr.bit_width = fallback_bits;
    annotateExprSlots(expr, slot_ids);
    annotateExprStackCells(expr, stack_cell_ids, slot_ids);
    expr = specializeExprToFixpoint(expr, state.slot_facts, &state.stack_facts,
                                    &incoming_args, slot_ids,
                                    stack_cell_ids);
    annotateExprSlots(expr, slot_ids);
    annotateExprStackCells(expr, stack_cell_ids, slot_ids);
    if (!expr.bit_width)
      expr.bit_width = fallback_bits;
    return expr;
  };
  auto canonicalize_slot = [&](VirtualStateSlotSummary slot) {
    slot.canonical_id = lookupSlotIdForSummary(slot, slot_ids);
    return slot;
  };
  auto canonicalize_cell = [&](VirtualStackCellSummary cell) {
    cell.canonical_id = lookupStackCellIdForSummary(cell, stack_cell_ids);
    VirtualStateSlotSummary base_slot;
    base_slot.base_name = cell.base_name;
    base_slot.offset = cell.base_offset;
    base_slot.width = cell.base_width;
    base_slot.from_argument = cell.base_from_argument;
    base_slot.from_alloca = cell.base_from_alloca;
    cell.canonical_base_slot_id = lookupSlotIdForSummary(base_slot, slot_ids);
    return cell;
  };
  auto render_update = [&](llvm::StringRef kind, unsigned id,
                           const VirtualValueExpr &value) {
    std::string rendered;
    llvm::raw_string_ostream os(rendered);
    os << kind << "[" << id << "] = " << renderVirtualValueExpr(value);
    return os.str();
  };
  auto log_stack_lookup = [&](llvm::StringRef source,
                              const VirtualStackCellSummary &cell,
                              std::optional<unsigned> direct_id,
                              std::optional<unsigned> rebased_id,
                              bool local_hit, bool rebased_hit,
                              bool caller_hit) {
    if (!vmModelLocalReplayDebugEnabled())
      return;
    std::string rendered;
    llvm::raw_string_ostream os(rendered);
    os << "helper=" << F.getName() << " " << source << " base=" << cell.base_name
       << "+" << cell.base_offset
       << " cell_off=" << cell.offset << " direct=";
    if (direct_id)
      os << *direct_id;
    else
      os << "none";
    if (direct_id) {
      auto it = llvm::find_if(model.stackCells(), [&](const auto &info) {
        return info.id == *direct_id;
      });
      if (it != model.stackCells().end())
        os << "(" << it->base_name << "+" << it->base_offset << ","
           << it->cell_offset << ")";
    }
    os << " rebased=";
    if (rebased_id)
      os << *rebased_id;
    else
      os << "none";
    if (rebased_id) {
      auto it = llvm::find_if(model.stackCells(), [&](const auto &info) {
        return info.id == *rebased_id;
      });
      if (it != model.stackCells().end())
        os << "(" << it->base_name << "+" << it->base_offset << ","
           << it->cell_offset << ")";
    }
    os << " local_hit=" << local_hit << " rebased_hit=" << rebased_hit
       << " caller_hit=" << caller_hit;
    vmModelLocalReplayDebugLog(os.str());
  };
  auto lookup_caller_stack_fact =
      [&](const VirtualStackCellSummary &cell) -> std::optional<VirtualValueExpr> {
    if (!caller_stack_facts)
      return std::nullopt;

    auto lookup_equivalent_caller_fact =
        [&](const VirtualStackCellSummary &query)
            -> std::optional<VirtualValueExpr> {
      std::optional<VirtualValueExpr> found;
      for (const auto &candidate : model.stackCells()) {
        if (candidate.base_offset != query.base_offset ||
            candidate.base_width != query.base_width ||
            candidate.cell_offset != query.offset ||
            candidate.width != query.width ||
            candidate.base_from_argument != query.base_from_argument ||
            candidate.base_from_alloca != query.base_from_alloca) {
          continue;
        }
        if (!query.base_from_argument && candidate.base_name != query.base_name)
          continue;
        auto it = caller_stack_facts->find(candidate.id);
        if (it == caller_stack_facts->end())
          continue;
        if (!found) {
          found = it->second;
          continue;
        }
        if (!exprEquals(*found, it->second))
          return std::nullopt;
      }
      return found;
    };

    auto direct_cell = canonicalize_cell(cell);
    if (direct_cell.canonical_id.has_value()) {
      unsigned direct_id = *direct_cell.canonical_id;
      if (auto it = caller_stack_facts->find(direct_id);
          it != caller_stack_facts->end()) {
        return it->second;
      }
      if (auto equivalent = lookup_equivalent_caller_fact(direct_cell))
        return equivalent;
      unsigned rebased_id =
          rebaseSingleStackCellId(model, state.slot_facts, direct_id);
      if (rebased_id != direct_id) {
        if (auto it = caller_stack_facts->find(rebased_id);
            it != caller_stack_facts->end()) {
          return it->second;
        }
        auto rebased_it = llvm::find_if(model.stackCells(), [&](const auto &info) {
          return info.id == rebased_id;
        });
        if (rebased_it != model.stackCells().end()) {
          VirtualStackCellSummary rebased_cell;
          rebased_cell.base_name = rebased_it->base_name;
          rebased_cell.base_offset = rebased_it->base_offset;
          rebased_cell.base_width = rebased_it->base_width;
          rebased_cell.base_from_argument = rebased_it->base_from_argument;
          rebased_cell.base_from_alloca = rebased_it->base_from_alloca;
          rebased_cell.offset = rebased_it->cell_offset;
          rebased_cell.width = rebased_it->width;
          rebased_cell.canonical_id = rebased_id;
          if (auto equivalent = lookup_equivalent_caller_fact(rebased_cell))
            return equivalent;
        }
      }
      if (caller_slot_facts) {
        unsigned caller_rebased_id =
            rebaseSingleStackCellId(model, *caller_slot_facts, direct_id);
        if (caller_rebased_id != direct_id) {
          if (auto it = caller_stack_facts->find(caller_rebased_id);
              it != caller_stack_facts->end()) {
            return it->second;
          }
          auto caller_rebased_it =
              llvm::find_if(model.stackCells(), [&](const auto &info) {
                return info.id == caller_rebased_id;
              });
          if (caller_rebased_it != model.stackCells().end()) {
            VirtualStackCellSummary caller_rebased_cell;
            caller_rebased_cell.base_name = caller_rebased_it->base_name;
            caller_rebased_cell.base_offset = caller_rebased_it->base_offset;
            caller_rebased_cell.base_width = caller_rebased_it->base_width;
            caller_rebased_cell.base_from_argument =
                caller_rebased_it->base_from_argument;
            caller_rebased_cell.base_from_alloca =
                caller_rebased_it->base_from_alloca;
            caller_rebased_cell.offset = caller_rebased_it->cell_offset;
            caller_rebased_cell.width = caller_rebased_it->width;
            caller_rebased_cell.canonical_id = caller_rebased_id;
            if (auto equivalent =
                    lookup_equivalent_caller_fact(caller_rebased_cell)) {
              return equivalent;
            }
          }
        }
      }
    }

    if (!localizing_call || !cell.base_from_argument)
      return std::nullopt;

    auto arg_index = parseArgumentBaseName(cell.base_name);
    if (!arg_index || *arg_index >= localizing_call->arg_size())
      return std::nullopt;

    auto *actual_arg = localizing_call->getArgOperand(*arg_index);
    VirtualStackCellSummary mapped_cell = cell;
    if (auto actual_slot =
            extractStateSlotSummary(actual_arg, cell.base_width, dl)) {
      mapped_cell.base_name = actual_slot->base_name;
      mapped_cell.base_offset += actual_slot->offset;
      mapped_cell.base_width = actual_slot->width;
      mapped_cell.base_from_argument = actual_slot->from_argument;
      mapped_cell.base_from_alloca = actual_slot->from_alloca;
    } else {
      auto actual_expr = summarizeValueExpr(actual_arg, dl);
      annotateExprSlots(actual_expr, slot_ids);
      annotateExprStackCells(actual_expr, stack_cell_ids, slot_ids);
      if (auto actual_cell = extractStackCellSummaryFromExpr(actual_expr,
                                                             cell.width)) {
        mapped_cell.base_name = actual_cell->base_name;
        mapped_cell.base_offset += actual_cell->base_offset;
        mapped_cell.base_width = actual_cell->base_width;
        mapped_cell.base_from_argument = actual_cell->base_from_argument;
        mapped_cell.base_from_alloca = actual_cell->base_from_alloca;
        mapped_cell.offset += actual_cell->offset;
      } else {
        return std::nullopt;
      }
    }

    auto canonical_mapped = canonicalize_cell(mapped_cell);
    if (!canonical_mapped.canonical_id.has_value())
      return std::nullopt;
    unsigned mapped_id = *canonical_mapped.canonical_id;
    if (auto it = caller_stack_facts->find(mapped_id);
        it != caller_stack_facts->end()) {
        return it->second;
      }
    unsigned rebased_mapped_id =
        rebaseSingleStackCellId(model, state.slot_facts, mapped_id);
    if (rebased_mapped_id == mapped_id)
      return std::nullopt;
    auto it = caller_stack_facts->find(rebased_mapped_id);
    return (it == caller_stack_facts->end()) ? std::nullopt
                                             : std::optional<VirtualValueExpr>(
                                                   it->second);
  };

  llvm::SmallPtrSet<const llvm::Value *, 16> visiting_values;
  std::function<std::optional<VirtualValueExpr>(llvm::Value *)> eval_value =
      [&](llvm::Value *value) -> std::optional<VirtualValueExpr> {
    if (!value)
      return std::nullopt;
    if (auto it = state.value_facts.find(value); it != state.value_facts.end())
      return it->second;

    if (!visiting_values.insert(value).second)
      return std::nullopt;
    auto pop_visited =
        llvm::make_scope_exit([&] { visiting_values.erase(value); });

    if (auto *ci = llvm::dyn_cast<llvm::ConstantInt>(value))
      return constantExpr(ci->getZExtValue(), ci->getBitWidth());
    if (llvm::isa<llvm::ConstantPointerNull>(value))
      return constantExpr(0, getValueBitWidth(value, dl));
    if (llvm::isa<llvm::UndefValue>(value) || llvm::isa<llvm::PoisonValue>(value))
      return unknownExpr(getValueBitWidth(value, dl));

    if (auto *arg = llvm::dyn_cast<llvm::Argument>(value)) {
      if (auto it = incoming_args.find(static_cast<unsigned>(arg->getArgNo()));
          it != incoming_args.end()) {
        return normalize_expr(it->second, getValueBitWidth(value, dl));
      }
      return argumentExpr(static_cast<unsigned>(arg->getArgNo()),
                          getValueBitWidth(value, dl));
    }

    auto cache_instruction_expr = [&](const VirtualValueExpr &expr) {
      if (auto *inst = llvm::dyn_cast<llvm::Instruction>(value))
        state.value_facts[inst] = expr;
    };

    if (auto *alloca = llvm::dyn_cast<llvm::AllocaInst>(value)) {
      auto alloc_size = dl.getTypeAllocSize(alloca->getAllocatedType());
      if (alloc_size.isScalable())
        return std::nullopt;
      if (alloca->isArrayAllocation()) {
        auto *array_size =
            llvm::dyn_cast<llvm::ConstantInt>(alloca->getArraySize());
        if (!array_size || !array_size->isOne())
          return std::nullopt;
      }

      VirtualStateSlotSummary slot;
      slot.base_name = alloca->getName().str();
      if (slot.base_name.empty())
        slot.base_name = "alloca";
      slot.offset = 0;
      slot.width = alloc_size.getFixedValue();
      slot.from_argument = false;
      slot.from_alloca = true;

      auto canonical_slot = canonicalize_slot(slot);
      VirtualValueExpr result;
      result.kind = VirtualExprKind::kStateSlot;
      result.complete = true;
      result.state_base_name = slot.base_name;
      result.state_offset = 0;
      result.slot_id = canonical_slot.canonical_id;
      result.bit_width = getValueBitWidth(value, dl);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(value)) {
      unsigned width_bytes =
          std::max(1u, dl.getPointerSize(gep->getType()->getPointerAddressSpace()));
      if (auto slot = extractStateSlotSummary(gep, width_bytes, dl)) {
        auto canonical_slot = canonicalize_slot(*slot);
        auto result =
            normalize_expr(stateSlotExpr(canonical_slot), getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }
      return std::nullopt;
    }

    if (auto *load = llvm::dyn_cast<llvm::LoadInst>(value)) {
      auto width = dl.getTypeStoreSize(load->getType());
      if (width.isScalable())
        return std::nullopt;

      if (auto slot = extractStateSlotSummary(load->getPointerOperand(),
                                              width.getFixedValue(), dl)) {
        auto canonical_slot = canonicalize_slot(*slot);
        VirtualValueExpr result = stateSlotExpr(canonical_slot);
        if (canonical_slot.canonical_id.has_value()) {
          if (auto it = state.slot_facts.find(*canonical_slot.canonical_id);
              it != state.slot_facts.end()) {
            result = normalize_expr(it->second, width.getFixedValue() * 8u);
          } else {
            result = normalize_expr(result, width.getFixedValue() * 8u);
          }
        } else {
          result = normalize_expr(result, width.getFixedValue() * 8u);
        }
        cache_instruction_expr(result);
        return result;
      }

      auto pointer_expr = eval_value(load->getPointerOperand());
      if (!pointer_expr)
        return std::nullopt;
      if (auto cell =
              extractStackCellSummaryFromExpr(*pointer_expr,
                                             width.getFixedValue())) {
        auto canonical_cell = canonicalize_cell(*cell);
        VirtualValueExpr result = stackCellExpr(canonical_cell);
        if (canonical_cell.canonical_id.has_value()) {
          unsigned cell_id = *canonical_cell.canonical_id;
          std::optional<unsigned> rebased_cell_id;
          bool local_hit = state.stack_facts.count(cell_id);
          bool rebased_hit = false;
          bool caller_hit = false;
          if (auto it = state.stack_facts.find(cell_id);
              it != state.stack_facts.end()) {
            result = normalize_expr(it->second, width.getFixedValue() * 8u);
          } else if ((rebased_cell_id =
                          rebaseSingleStackCellId(model, state.slot_facts,
                                                  cell_id)),
                     rebased_cell_id.has_value() &&
                     *rebased_cell_id != cell_id &&
                     (rebased_hit = state.stack_facts.count(*rebased_cell_id))) {
            result = normalize_expr(state.stack_facts.at(*rebased_cell_id),
                                    width.getFixedValue() * 8u);
          } else if (auto caller_value = lookup_caller_stack_fact(canonical_cell)) {
            caller_hit = true;
            result = normalize_expr(*caller_value, width.getFixedValue() * 8u);
          } else {
            result = normalize_expr(result, width.getFixedValue() * 8u);
          }
          log_stack_lookup("load", canonical_cell, cell_id, rebased_cell_id,
                           local_hit, rebased_hit, caller_hit);
        } else {
          result = normalize_expr(result, width.getFixedValue() * 8u);
        }
        cache_instruction_expr(result);
        return result;
      }

      return std::nullopt;
    }

    if (auto *cast = llvm::dyn_cast<llvm::CastInst>(value)) {
      switch (cast->getOpcode()) {
        case llvm::Instruction::ZExt:
        case llvm::Instruction::SExt:
        case llvm::Instruction::Trunc:
        case llvm::Instruction::BitCast:
        case llvm::Instruction::PtrToInt:
        case llvm::Instruction::IntToPtr: {
          auto inner = eval_value(cast->getOperand(0));
          if (!inner)
            return std::nullopt;
          auto result = *inner;
          result.bit_width = getValueBitWidth(value, dl);
          result = normalize_expr(result, result.bit_width);
          cache_instruction_expr(result);
          return result;
        }
        default:
          return std::nullopt;
      }
    }

    if (auto *bin = llvm::dyn_cast<llvm::BinaryOperator>(value)) {
      auto kind = classifyExprKind(bin->getOpcode());
      switch (kind) {
        case VirtualExprKind::kAdd:
        case VirtualExprKind::kSub:
        case VirtualExprKind::kXor:
        case VirtualExprKind::kAnd:
        case VirtualExprKind::kOr:
        case VirtualExprKind::kShl:
        case VirtualExprKind::kLShr:
        case VirtualExprKind::kAShr:
          break;
        default:
          return std::nullopt;
      }
      auto lhs = eval_value(bin->getOperand(0));
      auto rhs = eval_value(bin->getOperand(1));
      if (!lhs || !rhs)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = kind;
      result.bit_width = getValueBitWidth(value, dl);
      result.complete = lhs->complete && rhs->complete;
      result.operands.push_back(*lhs);
      result.operands.push_back(*rhs);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *icmp = llvm::dyn_cast<llvm::ICmpInst>(value)) {
      auto kind = classifyICmpPredicate(icmp->getPredicate());
      if (kind == VirtualExprKind::kUnknown)
        return std::nullopt;
      auto lhs = eval_value(icmp->getOperand(0));
      auto rhs = eval_value(icmp->getOperand(1));
      if (!lhs || !rhs)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = kind;
      result.bit_width = 1;
      result.complete = lhs->complete && rhs->complete;
      result.operands.push_back(*lhs);
      result.operands.push_back(*rhs);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *select = llvm::dyn_cast<llvm::SelectInst>(value)) {
      auto cond = eval_value(select->getCondition());
      auto true_value = eval_value(select->getTrueValue());
      auto false_value = eval_value(select->getFalseValue());
      if (!cond || !true_value || !false_value)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = VirtualExprKind::kSelect;
      result.bit_width = getValueBitWidth(value, dl);
      result.complete =
          cond->complete && true_value->complete && false_value->complete;
      result.operands.push_back(*cond);
      result.operands.push_back(*true_value);
      result.operands.push_back(*false_value);
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *phi = llvm::dyn_cast<llvm::PHINode>(value)) {
      if (phi->getNumIncomingValues() == 0 || phi->getNumIncomingValues() > 4)
        return std::nullopt;
      VirtualValueExpr result;
      result.kind = VirtualExprKind::kPhi;
      result.bit_width = getValueBitWidth(value, dl);
      result.complete = true;
      for (llvm::Value *incoming : phi->incoming_values()) {
        auto incoming_expr = eval_value(incoming);
        if (!incoming_expr)
          return std::nullopt;
        result.complete &= incoming_expr->complete;
        result.operands.push_back(*incoming_expr);
      }
      result = normalize_expr(result, result.bit_width);
      cache_instruction_expr(result);
      return result;
    }

    if (auto *call = llvm::dyn_cast<llvm::CallBase>(value)) {
      auto *callee = call->getCalledFunction();
      if (!callee)
        return std::nullopt;

      if (isRemillReadMemoryIntrinsic(*callee) && call->arg_size() >= 2) {
        unsigned width_bits =
            remillMemoryBitWidth(callee->getName())
                .value_or(getValueBitWidth(value, dl));
        unsigned width_bytes = std::max(1u, width_bits / 8u);
        auto address_expr = eval_value(call->getArgOperand(1));
        if (!address_expr)
          return std::nullopt;
        if (auto cell =
                extractStackCellSummaryFromExpr(*address_expr,
                                               width_bytes)) {
          auto canonical_cell = canonicalize_cell(*cell);
          VirtualValueExpr result = stackCellExpr(canonical_cell);
          if (canonical_cell.canonical_id.has_value()) {
            unsigned cell_id = *canonical_cell.canonical_id;
            std::optional<unsigned> rebased_cell_id;
            bool local_hit = state.stack_facts.count(cell_id);
            bool rebased_hit = false;
            bool caller_hit = false;
            if (auto it = state.stack_facts.find(cell_id);
                it != state.stack_facts.end()) {
              result = normalize_expr(it->second, width_bits);
            } else if ((rebased_cell_id =
                            rebaseSingleStackCellId(model, state.slot_facts,
                                                    cell_id)),
                       rebased_cell_id.has_value() &&
                       *rebased_cell_id != cell_id &&
                       (rebased_hit = state.stack_facts.count(*rebased_cell_id))) {
              result = normalize_expr(state.stack_facts.at(*rebased_cell_id),
                                      width_bits);
            } else if (auto caller_value =
                           lookup_caller_stack_fact(canonical_cell)) {
              caller_hit = true;
              result = normalize_expr(*caller_value, width_bits);
            } else {
              result = normalize_expr(result, width_bits);
            }
            log_stack_lookup("readmem", canonical_cell, cell_id, rebased_cell_id,
                             local_hit, rebased_hit, caller_hit);
          } else {
            result = normalize_expr(result, width_bits);
          }
          cache_instruction_expr(result);
          return result;
        }
        return std::nullopt;
      }

      if (isRemillWriteMemoryIntrinsic(*callee) && call->arg_size() >= 1) {
        auto memory_expr = eval_value(call->getArgOperand(0));
        if (!memory_expr)
          return std::nullopt;
        auto result = normalize_expr(*memory_expr, getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }

      if (handler_index.find(callee->getName().str()) != handler_index.end() &&
          call->arg_size() >= 1) {
        auto memory_expr = eval_value(call->getArgOperand(0));
        if (!memory_expr)
          return std::nullopt;
        auto result = normalize_expr(*memory_expr, getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }

      if (isRemillTerminalControlIntrinsic(*callee) && call->arg_size() >= 1) {
        auto memory_expr = eval_value(call->getArgOperand(0));
        if (!memory_expr)
          return std::nullopt;
        auto result = normalize_expr(*memory_expr, getValueBitWidth(value, dl));
        cache_instruction_expr(result);
        return result;
      }

      return std::nullopt;
    }

    auto fallback = summarizeValueExpr(value, dl);
    if (fallback.kind == VirtualExprKind::kUnknown)
      return std::nullopt;
    fallback = normalize_expr(fallback, getValueBitWidth(value, dl));
    if (auto *inst = llvm::dyn_cast<llvm::Instruction>(value))
      state.value_facts[inst] = fallback;
    return fallback;
  };

  auto cache_instruction_value = [&](llvm::Instruction &I) {
    if (I.getType()->isVoidTy())
      return true;
    if (llvm::isa<llvm::StoreInst>(I))
      return true;
    auto expr = eval_value(&I);
    if (!expr) {
      vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                 " reason=unsupported-value inst=" +
                                 std::string(I.getOpcodeName()));
      return false;
    }
    state.value_facts[&I] = *expr;
    return true;
  };

  for (auto *BB : *replay_blocks) {
    for (auto &I : *BB) {
      if (!cache_instruction_value(I))
        return std::nullopt;

      if (auto *store = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        auto width = dl.getTypeStoreSize(store->getValueOperand()->getType());
        if (width.isScalable()) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=scalable-store");
          return std::nullopt;
        }

        auto value_expr = eval_value(store->getValueOperand());
        if (!value_expr) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=store-value");
          return std::nullopt;
        }
        auto normalized_value = *value_expr;
        if (!normalized_value.bit_width)
          normalized_value.bit_width = width.getFixedValue() * 8u;
        if (auto slot = extractStateSlotSummary(store->getPointerOperand(),
                                                width.getFixedValue(), dl)) {
          auto canonical_slot = canonicalize_slot(*slot);
          if (!canonical_slot.canonical_id.has_value()) {
            vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                       " reason=unknown-store-slot");
            return std::nullopt;
          }
          state.slot_facts[*canonical_slot.canonical_id] = normalized_value;
          vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                     render_update("slot",
                                                   *canonical_slot.canonical_id,
                                                   normalized_value));
          continue;
        }

        auto pointer_expr = eval_value(store->getPointerOperand());
        if (!pointer_expr) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=store-pointer");
          return std::nullopt;
        }
        auto cell = extractStackCellSummaryFromExpr(*pointer_expr,
                                                    width.getFixedValue());
        if (!cell) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=store-target");
          return std::nullopt;
        }
        auto canonical_cell = canonicalize_cell(*cell);
        if (!canonical_cell.canonical_id.has_value()) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=unknown-store-cell");
          return std::nullopt;
        }
        state.stack_facts[*canonical_cell.canonical_id] = normalized_value;
        vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                   render_update("cell",
                                                 *canonical_cell.canonical_id,
                                                 normalized_value));
        continue;
      }

      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;

      auto *callee = call->getCalledFunction();
      if (!callee) {
        vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                   " reason=indirect-call");
        return std::nullopt;
      }
      if (isRemillReadMemoryIntrinsic(*callee))
        continue;
      if (isRemillTerminalControlIntrinsic(*callee))
        continue;
      if (isRemillWriteMemoryIntrinsic(*callee)) {
        if (call->arg_size() < 3) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=short-write-memory");
          return std::nullopt;
        }

        unsigned width_bits = remillMemoryBitWidth(callee->getName()).value_or(0);
        unsigned width_bytes = std::max(1u, width_bits / 8u);
        auto address_expr = eval_value(call->getArgOperand(1));
        auto value_expr = eval_value(call->getArgOperand(2));
        if (!address_expr || !value_expr) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=write-memory-operands");
          return std::nullopt;
        }
        auto normalized_value = *value_expr;
        if (!normalized_value.bit_width)
          normalized_value.bit_width = std::max(1u, width_bits);
        auto cell = extractStackCellSummaryFromExpr(*address_expr, width_bytes);
        if (!cell) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=write-memory-target");
          return std::nullopt;
        }
        auto canonical_cell = canonicalize_cell(*cell);
        if (!canonical_cell.canonical_id.has_value()) {
          vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                     " reason=unknown-write-memory-cell");
          return std::nullopt;
        }
        state.stack_facts[*canonical_cell.canonical_id] = normalized_value;
        vmModelLocalReplayDebugLog("helper=" + F.getName().str() + " " +
                                   render_update("cell",
                                                 *canonical_cell.canonical_id,
                                                 normalized_value));
        continue;
      }

      if (applySingleDirectCalleeEffects(
              F, *call, model, handler_index, outgoing_maps,
              outgoing_stack_maps, incoming_args, state.slot_facts,
              state.stack_facts, slot_ids, slot_info, stack_cell_ids,
              stack_cell_info, dl, depth, visiting)) {
        specializeFactStateToFixpoint(state.slot_facts, state.stack_facts,
                                      &incoming_args, slot_ids,
                                      stack_cell_ids);
        vmModelLocalReplayDebugLog("helper=" + F.getName().str() +
                                   " direct-call-localized=" +
                                   callee->getName().str());
        continue;
      }

      vmModelLocalReplayDebugLog("bail helper=" + F.getName().str() +
                                 " reason=unsupported-call callee=" +
                                 callee->getName().str());
      return std::nullopt;
    }
  }

  CallsiteLocalizedOutgoingFacts localized;
  localized.outgoing_slots = std::move(state.slot_facts);
  localized.outgoing_stack = std::move(state.stack_facts);
  return localized;
}

static std::optional<uint64_t> resolveSpecializedExprToConstant(
    const VirtualValueExpr &expr,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack) {
  if (expr.constant.has_value())
    return expr.constant;
  auto slot_facts = slotFactsForMap(caller_outgoing);
  auto stack_facts = stackFactsForMap(caller_outgoing_stack);
  return evaluateVirtualExpr(expr, slot_facts, stack_facts);
}

static void seedNamedSlotFact(const std::map<SlotKey, unsigned> &slot_ids,
                              llvm::StringRef base_name, uint64_t value,
                              std::map<unsigned, VirtualValueExpr> &slot_facts) {
  auto it = llvm::find_if(slot_ids, [&](const auto &entry) {
    return entry.first.base_name == base_name && entry.first.offset == 0;
  });
  if (it == slot_ids.end())
    return;
  unsigned width_bits = it->first.width ? it->first.width * 8 : 64;
  slot_facts[it->second] = constantExpr(value, width_bits);
}

static std::optional<unsigned> lookupNamedSlotId(
    const std::map<SlotKey, unsigned> &slot_ids, llvm::StringRef base_name) {
  auto it = llvm::find_if(slot_ids, [&](const auto &entry) {
    return entry.first.base_name == base_name && entry.first.offset == 0;
  });
  if (it == slot_ids.end())
    return std::nullopt;
  return it->second;
}

static bool exprMatchesSlot(const VirtualValueExpr &expr, unsigned slot_id) {
  if (expr.kind != VirtualExprKind::kStateSlot || !expr.slot_id.has_value())
    return false;
  return *expr.slot_id == slot_id;
}

static bool exprMatchesBasePlusOrMinusConst(const VirtualValueExpr &expr,
                                            unsigned slot_id,
                                            VirtualExprKind &op_kind,
                                            uint64_t &imm) {
  if (expr.kind == VirtualExprKind::kAdd && expr.operands.size() == 2) {
    if (exprMatchesSlot(expr.operands[0], slot_id) &&
        expr.operands[1].constant.has_value()) {
      op_kind = VirtualExprKind::kAdd;
      imm = *expr.operands[1].constant;
      return true;
    }
    if (expr.operands[0].constant.has_value() &&
        exprMatchesSlot(expr.operands[1], slot_id)) {
      op_kind = VirtualExprKind::kAdd;
      imm = *expr.operands[0].constant;
      return true;
    }
  }

  if (expr.kind == VirtualExprKind::kSub && expr.operands.size() == 2 &&
      exprMatchesSlot(expr.operands[0], slot_id) &&
      expr.operands[1].constant.has_value()) {
    op_kind = VirtualExprKind::kSub;
    imm = *expr.operands[1].constant;
    return true;
  }

  return false;
}

static bool isReturnPcAnchoredOutgoingNextPcForCallsiteTarget(
    const VirtualValueExpr &callsite_target, const VirtualValueExpr &next_pc_expr,
    unsigned next_pc_slot_id, unsigned return_pc_slot_id) {
  VirtualExprKind callsite_op = VirtualExprKind::kUnknown;
  VirtualExprKind next_pc_op = VirtualExprKind::kUnknown;
  uint64_t callsite_imm = 0;
  uint64_t next_pc_imm = 0;
  if (!exprMatchesBasePlusOrMinusConst(callsite_target, next_pc_slot_id,
                                       callsite_op, callsite_imm)) {
    return false;
  }
  if (!exprMatchesBasePlusOrMinusConst(next_pc_expr, return_pc_slot_id,
                                       next_pc_op, next_pc_imm)) {
    return false;
  }
  return callsite_op == next_pc_op && callsite_imm == next_pc_imm;
}

static std::optional<ResolvedCallSiteInfo>
resolveCallSiteInfoFromOutgoingNextPc(
    const VirtualHandlerSummary &summary, const VirtualValueExpr &callsite_target,
    std::optional<uint64_t> continuation_pc,
    const std::map<SlotKey, unsigned> &slot_ids) {
  if (!continuation_pc)
    return std::nullopt;

  auto next_pc_slot_id = lookupNamedSlotId(slot_ids, "NEXT_PC");
  auto return_pc_slot_id = lookupNamedSlotId(slot_ids, "RETURN_PC");
  if (!next_pc_slot_id || !return_pc_slot_id)
    return std::nullopt;

  const VirtualSlotFact *next_pc_fact = nullptr;
  for (const auto &fact : summary.outgoing_facts) {
    if (fact.slot_id == *next_pc_slot_id) {
      next_pc_fact = &fact;
      break;
    }
  }
  if (!next_pc_fact)
    return std::nullopt;

  if (!isReturnPcAnchoredOutgoingNextPcForCallsiteTarget(
          callsite_target, next_pc_fact->value, *next_pc_slot_id,
          *return_pc_slot_id)) {
    return std::nullopt;
  }

  auto seeded_slot_facts = summary.outgoing_facts;
  auto return_fact_it =
      llvm::find_if(seeded_slot_facts, [&](const VirtualSlotFact &fact) {
        return fact.slot_id == *return_pc_slot_id;
      });
  VirtualValueExpr return_pc_expr =
      constantExpr(*continuation_pc, next_pc_fact->value.bit_width
                                         ? next_pc_fact->value.bit_width
                                         : 64);
  if (return_fact_it == seeded_slot_facts.end()) {
    seeded_slot_facts.push_back(
        VirtualSlotFact{*return_pc_slot_id, std::move(return_pc_expr)});
  } else {
    return_fact_it->value = std::move(return_pc_expr);
  }

  auto resolved_pc = evaluateVirtualExpr(next_pc_fact->value, seeded_slot_facts,
                                         summary.outgoing_stack_facts);
  if (!resolved_pc)
    return std::nullopt;

  ResolvedCallSiteInfo info;
  info.target_expr = next_pc_fact->value;
  info.target_source = VirtualDispatchResolutionSource::kOutgoingFacts;
  info.target_pc = resolved_pc;
  info.continuation_pc = continuation_pc;
  return info;
}

static ResolvedCallSiteInfo resolveCallSiteInfo(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  ResolvedCallSiteInfo info;
  std::map<unsigned, VirtualValueExpr> callsite_slots = caller_outgoing;
  std::map<unsigned, VirtualValueExpr> callsite_stack = caller_outgoing_stack;

  if (call.arg_size() >= 5) {
    auto continuation_expr = summarizeSpecializedCallArg(
        call, 4, dl, slot_ids, stack_cell_ids, callsite_slots, callsite_stack,
        caller_argument_map);
    info.continuation_pc =
        resolveSpecializedExprToConstant(continuation_expr, callsite_slots,
                                         callsite_stack);
  }
  if (!info.continuation_pc)
    info.continuation_pc = inferLiftedCallContinuationPc(call);
  if (info.continuation_pc.has_value()) {
    seedNamedSlotFact(slot_ids, "RETURN_PC", *info.continuation_pc,
                      callsite_slots);
    specializeFactStateToFixpoint(callsite_slots, callsite_stack,
                                  &caller_argument_map, slot_ids,
                                  stack_cell_ids);
  }

  if (call.arg_size() >= 3) {
    auto direct_target = summarizeValueExpr(call.getArgOperand(2), dl);
    annotateExprSlots(direct_target, slot_ids);
    annotateExprStackCells(direct_target, stack_cell_ids, slot_ids);
    auto specialized_target = specializeExprToFixpoint(
        direct_target, callsite_slots, &callsite_stack, &caller_argument_map,
        slot_ids, stack_cell_ids);
    info.target_expr = specialized_target;
    info.target_source = exprEquals(specialized_target, direct_target)
                             ? VirtualDispatchResolutionSource::kDirect
                             : VirtualDispatchResolutionSource::
                                   kHelperArgumentSpecialization;
    info.target_pc =
        resolveSpecializedExprToConstant(specialized_target, callsite_slots,
                                         callsite_stack);
  }
  return info;
}

static void seedCallContinuationStackCell(
    llvm::Module &M, uint64_t continuation_pc,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    std::map<unsigned, VirtualValueExpr> &callee_incoming_stack) {
  auto sp_offset = lookupNativeStackPointerOffset(M);
  if (!sp_offset)
    return;

  for (const auto &[cell_id, cell] : stack_cell_info) {
    if (!cell->base_from_argument || cell->base_from_alloca)
      continue;
    auto arg_index = parseArgumentBaseName(cell->base_name);
    if (!arg_index || *arg_index != 0)
      continue;
    if (cell->base_offset != static_cast<int64_t>(*sp_offset) ||
        cell->cell_offset != 0) {
      continue;
    }
    callee_incoming_stack[cell_id] =
        constantExpr(continuation_pc, cell->width * 8);
  }
}

static void seedLiftedCallContinuationStackCell(
    llvm::CallBase &call, const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    std::map<unsigned, VirtualValueExpr> &callee_incoming_stack) {
  (void) callee_summary;
  auto continuation_pc = inferLiftedCallContinuationPc(call);
  if (!continuation_pc)
    return;

  auto *module = call.getModule();
  if (!module)
    return;
  seedCallContinuationStackCell(*module, *continuation_pc, stack_cell_info,
                                callee_incoming_stack);
}

static std::optional<CallsiteLocalizedOutgoingFacts>
computeCallsiteLocalizedOutgoingFacts(
    llvm::CallBase &call, const VirtualMachineModel &model,
    const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  auto *callee_fn = call.getCalledFunction();
  if (!callee_fn)
    return std::nullopt;
  if (!canRecursivelyLocalizeCallsiteSummary(callee_summary, depth))
    return std::nullopt;
  if (!visiting.insert(callee_fn).second)
    return std::nullopt;

  std::map<unsigned, VirtualValueExpr> callee_incoming;
  std::map<unsigned, VirtualValueExpr> callee_incoming_stack;
  std::map<unsigned, VirtualValueExpr> callee_incoming_args;
  const auto specialized_call_args = buildSpecializedCallArgumentMap(
      call, dl, slot_ids, stack_cell_ids, caller_outgoing,
      caller_outgoing_stack, caller_argument_map);

  for (const auto &fact : callee_summary.specialization_facts)
    callee_incoming[fact.slot_id] = fact.value;
  for (const auto &fact : callee_summary.specialization_stack_facts)
    callee_incoming_stack[fact.cell_id] = fact.value;
  if (callee_summary.entry_va.has_value())
    callee_incoming_args[1] = constantExpr(*callee_summary.entry_va, 64);

  if (!callee_summary.direct_callees.empty()) {
    for (const auto &[slot_id, value] : caller_outgoing) {
      auto info_it = slot_info.find(slot_id);
      if (info_it == slot_info.end() || !info_it->second->from_argument ||
          !isBoundedStateProvenanceExpr(value)) {
        continue;
      }
      mergeFactIntoMap(callee_incoming, slot_id, value);
    }
    for (const auto &[cell_id, value] : caller_outgoing_stack) {
      auto info_it = stack_cell_info.find(cell_id);
      if (info_it == stack_cell_info.end() ||
          !info_it->second->base_from_argument ||
          !isBoundedStateProvenanceExpr(value)) {
        continue;
      }
      mergeFactIntoMap(callee_incoming_stack, cell_id, value);
    }
  }

  for (unsigned callee_slot_id : callee_summary.live_in_slot_ids) {
    if (auto same_it = caller_outgoing.find(callee_slot_id);
        same_it != caller_outgoing.end() &&
        isBoundedStateProvenanceExpr(same_it->second)) {
      mergeFactIntoMap(callee_incoming, callee_slot_id, same_it->second);
    }

    auto info_it = slot_info.find(callee_slot_id);
    if (info_it == slot_info.end())
      continue;
    std::optional<unsigned> mapped_slot_id;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name);
        arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStateSlotSummary mapped_slot = *actual_slot;
          mapped_slot.offset += info_it->second->offset;
          mapped_slot.width = info_it->second->width;
          mapped_slot_id = lookupSlotIdForSummary(mapped_slot, slot_ids);
        }
      }
    }
    if (!mapped_slot_id)
      mapped_slot_id =
          lookupMappedCallerSlotId(call, *info_it->second, slot_ids, dl);
    if (!mapped_slot_id)
      continue;
    auto value_it = caller_outgoing.find(*mapped_slot_id);
    if (value_it == caller_outgoing.end() ||
        !isSimpleRemappableFactExpr(value_it->second)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming, callee_slot_id, value_it->second);
  }

  for (unsigned callee_cell_id : callee_summary.live_in_stack_cell_ids) {
    if (auto same_it = caller_outgoing_stack.find(callee_cell_id);
        same_it != caller_outgoing_stack.end() &&
        isBoundedStateProvenanceExpr(same_it->second)) {
      mergeFactIntoMap(callee_incoming_stack, callee_cell_id, same_it->second);
    }

    auto info_it = stack_cell_info.find(callee_cell_id);
    if (info_it == stack_cell_info.end())
      continue;
    std::optional<unsigned> mapped_cell_id;
    if (auto arg_index = parseArgumentBaseName(info_it->second->base_name);
        arg_index) {
      if (auto expr_it = specialized_call_args.find(*arg_index);
          expr_it != specialized_call_args.end()) {
        if (auto actual_slot =
                extractStateSlotSummaryFromExpr(expr_it->second, slot_info)) {
          VirtualStackCellSummary mapped_cell;
          mapped_cell.base_name = actual_slot->base_name;
          mapped_cell.base_offset =
              actual_slot->offset + info_it->second->base_offset;
          mapped_cell.base_width = actual_slot->width;
          mapped_cell.base_from_argument = actual_slot->from_argument;
          mapped_cell.base_from_alloca = actual_slot->from_alloca;
          mapped_cell.offset = info_it->second->cell_offset;
          mapped_cell.width = info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        } else if (auto actual_cell = extractStackCellSummaryFromExpr(
                       expr_it->second, info_it->second->width)) {
          VirtualStackCellSummary mapped_cell = *actual_cell;
          mapped_cell.offset += info_it->second->cell_offset;
          mapped_cell.width = info_it->second->width;
          mapped_cell_id =
              lookupStackCellIdForSummary(mapped_cell, stack_cell_ids);
        }
      }
    }
    if (!mapped_cell_id) {
      mapped_cell_id = lookupMappedCallerStackCellId(
          call, *info_it->second, slot_ids, stack_cell_ids, dl);
    }
    if (!mapped_cell_id)
      continue;
    auto value_it = caller_outgoing_stack.find(*mapped_cell_id);
    if (value_it == caller_outgoing_stack.end() ||
        !isSimpleRemappableFactExpr(value_it->second)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming_stack, callee_cell_id, value_it->second);
  }

  for (const auto &[arg_index, specialized] : specialized_call_args) {
    if (!isBoundedArgumentFactExpr(specialized))
      continue;
    mergeFactIntoMap(callee_incoming_args, arg_index, specialized);
  }

  seedLiftedCallContinuationStackCell(call, callee_summary, stack_cell_info,
                                      callee_incoming_stack);

  CallsiteLocalizedOutgoingFacts localized;
  if (canComputeLocalizedSingleBlockOutgoingFacts(*callee_fn, callee_summary)) {
    if (auto leaf_localized = computeLocalizedSingleBlockOutgoingFacts(
            *callee_fn, model, callee_summary, slot_ids, stack_cell_ids,
            callee_incoming, callee_incoming_stack, callee_incoming_args,
            handler_index, outgoing_maps, outgoing_stack_maps, depth, visiting,
            &call, &caller_outgoing_stack, &caller_outgoing)) {
      visiting.erase(callee_fn);
      return leaf_localized;
    }
  }

  for (const auto &fact : computeOutgoingFacts(callee_summary, callee_incoming,
                                               callee_incoming_stack,
                                               callee_incoming_args)) {
    localized.outgoing_slots.emplace(fact.slot_id, fact.value);
  }
  for (const auto &fact :
       computeOutgoingStackFacts(callee_summary, callee_incoming,
                                 callee_incoming_stack, callee_incoming_args)) {
    localized.outgoing_stack.emplace(fact.cell_id, fact.value);
  }
  if (!callee_summary.direct_callees.empty())
    applyDirectCalleeEffectsImpl(
        *callee_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming_args, localized.outgoing_slots, localized.outgoing_stack,
        slot_ids, slot_info, stack_cell_ids, stack_cell_info, dl, depth,
        visiting);
  if (!callee_summary.callsites.empty())
    applyLocalizedCallsiteReturnEffects(
        *callee_fn, model, callee_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming, callee_incoming_stack, callee_incoming_args,
        localized.outgoing_slots, localized.outgoing_stack, depth, visiting);
  if (!callee_summary.direct_callees.empty()) {
    const auto snapshot_slots = localized.outgoing_slots;
    const auto snapshot_stack = localized.outgoing_stack;
    for (auto &[slot_id, value] : localized.outgoing_slots) {
      (void) slot_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[cell_id, value] : localized.outgoing_stack) {
      (void) cell_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
  }
  localized.outgoing_stack =
      rebaseOutgoingStackFacts(model, localized.outgoing_slots,
                               localized.outgoing_stack);
  visiting.erase(callee_fn);
  return localized;
}

static std::optional<CallsiteLocalizedOutgoingFacts>
computeResolvedCallTargetOutgoingFacts(
    llvm::CallBase &call, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    const ResolvedCallSiteInfo &callsite, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  auto *target_fn = call.getModule()
                        ? call.getModule()->getFunction(target_summary.function_name)
                        : nullptr;
  if (!target_fn)
    return std::nullopt;
  if (depth > kMaxCallsiteLocalizationDepth)
    return std::nullopt;
  if (!callsite.target_pc.has_value())
    return std::nullopt;

  auto state_arg = summarizeSpecializedCallArg(
      call, 1, dl, slot_ids, stack_cell_ids, caller_outgoing,
      caller_outgoing_stack, caller_argument_map);
  if (!isCallerStateArgumentExpr(state_arg))
    return std::nullopt;

  if (!visiting.insert(target_fn).second)
    return std::nullopt;

  std::map<unsigned, VirtualValueExpr> callee_incoming;
  std::map<unsigned, VirtualValueExpr> callee_incoming_stack;
  std::map<unsigned, VirtualValueExpr> callee_incoming_args;

  for (const auto &fact : target_summary.specialization_facts)
    callee_incoming[fact.slot_id] = fact.value;
  for (const auto &fact : target_summary.specialization_stack_facts)
    callee_incoming_stack[fact.cell_id] = fact.value;

  callee_incoming_args[0] = state_arg;
  callee_incoming_args[1] = constantExpr(*callsite.target_pc, 64);
  if (call.arg_size() >= 1) {
    auto memory_arg = summarizeSpecializedCallArg(
        call, 0, dl, slot_ids, stack_cell_ids, caller_outgoing,
        caller_outgoing_stack, caller_argument_map);
    if (isBoundedArgumentFactExpr(memory_arg))
      callee_incoming_args[2] = std::move(memory_arg);
  }

  for (unsigned slot_id : target_summary.live_in_slot_ids) {
    auto value_it = caller_outgoing.find(slot_id);
    if (value_it == caller_outgoing.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming, slot_id, value_it->second);
  }
  for (unsigned cell_id : target_summary.live_in_stack_cell_ids) {
    auto value_it = caller_outgoing_stack.find(cell_id);
    if (value_it == caller_outgoing_stack.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming_stack, cell_id, value_it->second);
  }

  if (callsite.continuation_pc.has_value() && call.getModule()) {
    seedCallContinuationStackCell(*call.getModule(), *callsite.continuation_pc,
                                  stack_cell_info, callee_incoming_stack);
  }

  CallsiteLocalizedOutgoingFacts localized;
  if (canComputeLocalizedSingleBlockOutgoingFacts(*target_fn, target_summary)) {
    if (auto leaf_localized = computeLocalizedSingleBlockOutgoingFacts(
            *target_fn, model, target_summary, slot_ids, stack_cell_ids,
            callee_incoming, callee_incoming_stack, callee_incoming_args,
            handler_index, outgoing_maps, outgoing_stack_maps, depth, visiting,
            nullptr, nullptr, &caller_outgoing)) {
      visiting.erase(target_fn);
      return leaf_localized;
    }
  }

  for (const auto &fact : computeOutgoingFacts(target_summary, callee_incoming,
                                               callee_incoming_stack,
                                               callee_incoming_args)) {
    localized.outgoing_slots.emplace(fact.slot_id, fact.value);
  }
  for (const auto &fact :
       computeOutgoingStackFacts(target_summary, callee_incoming,
                                 callee_incoming_stack, callee_incoming_args)) {
    localized.outgoing_stack.emplace(fact.cell_id, fact.value);
  }

  if (!target_summary.direct_callees.empty()) {
    applyDirectCalleeEffectsImpl(
        *target_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming_args, localized.outgoing_slots, localized.outgoing_stack,
        slot_ids, slot_info, stack_cell_ids, stack_cell_info, dl, depth,
        visiting);
  }
  if (!target_summary.callsites.empty()) {
    applyLocalizedCallsiteReturnEffects(
        *target_fn, model, target_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming, callee_incoming_stack, callee_incoming_args,
        localized.outgoing_slots, localized.outgoing_stack, depth, visiting);
  }
  if (!target_summary.direct_callees.empty() || !target_summary.callsites.empty()) {
    const auto snapshot_slots = localized.outgoing_slots;
    const auto snapshot_stack = localized.outgoing_stack;
    for (auto &[slot_id, value] : localized.outgoing_slots) {
      (void) slot_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[cell_id, value] : localized.outgoing_stack) {
      (void) cell_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
  }

  localized.outgoing_stack =
      rebaseOutgoingStackFacts(model, localized.outgoing_slots,
                               localized.outgoing_stack);
  visiting.erase(target_fn);
  return localized;
}

static void applyLocalizedCallsiteReturnEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const VirtualHandlerSummary &caller_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    unsigned depth, llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  const auto &dl = caller_fn.getParent()->getDataLayout();

  size_t callsite_index = 0;
  for (auto &BB : caller_fn) {
    for (auto &I : BB) {
      auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isCallSiteHelper(*callee))
        continue;
      if (callsite_index >= caller_summary.callsites.size())
        continue;
      ++callsite_index;

      auto local_state = computeLocalFactsBeforeCall(
          *call, dl, slot_ids, stack_cell_ids, caller_incoming,
          caller_incoming_stack, caller_argument_map);
      auto resolved = resolveCallSiteInfo(
          *call, dl, slot_ids, stack_cell_ids, local_state.slot_facts,
          local_state.stack_facts, caller_argument_map);
      auto resolved_slot_facts = local_state.slot_facts;
      auto resolved_stack_facts = local_state.stack_facts;

      if (!resolved.target_pc.has_value()) {
        auto outgoing_local_state = computeLocalFactsBeforeCall(
            *call, dl, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, caller_argument_map);
        auto outgoing_resolved = resolveCallSiteInfo(
            *call, dl, slot_ids, stack_cell_ids,
            outgoing_local_state.slot_facts, outgoing_local_state.stack_facts,
            caller_argument_map);
        if (outgoing_resolved.target_pc.has_value()) {
          resolved = std::move(outgoing_resolved);
          resolved_slot_facts = std::move(outgoing_local_state.slot_facts);
          resolved_stack_facts = std::move(outgoing_local_state.stack_facts);
        }
      }

      if (!resolved.target_pc.has_value())
        continue;

      const auto *target_summary =
          lookupHandlerByEntryVA(model, *resolved.target_pc);
      if (!target_summary)
        continue;

      auto localized = computeResolvedCallTargetOutgoingFacts(
          *call, model, *target_summary, slot_info, stack_cell_info, slot_ids,
          stack_cell_ids, dl, handler_index, outgoing_maps, outgoing_stack_maps,
          resolved_slot_facts, resolved_stack_facts, caller_argument_map,
          resolved, depth + 1, visiting);
      if (!localized)
        continue;

      llvm::SmallDenseSet<unsigned, 16> written_slots(
          target_summary->written_slot_ids.begin(),
          target_summary->written_slot_ids.end());
      auto written_stack_cells = rebaseWrittenStackCellIds(
          model, localized->outgoing_slots, target_summary->written_stack_cell_ids);

      for (const auto &[slot_id, value] : localized->outgoing_slots) {
        if (!written_slots.empty() && !written_slots.count(slot_id))
          continue;
        auto normalized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, caller_argument_map);
        if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
            !isBoundedStateProvenanceExpr(*normalized)) {
          continue;
        }
        mergeFactIntoMap(caller_outgoing, slot_id, *normalized);
      }

      for (const auto &[cell_id, value] : localized->outgoing_stack) {
        if (!written_stack_cells.empty() && !written_stack_cells.count(cell_id))
          continue;
        auto normalized = normalizeLocalizedExprForCaller(
            value, caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
            caller_outgoing_stack, caller_argument_map);
        if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
            !isBoundedStateProvenanceExpr(*normalized)) {
          continue;
        }
        mergeFactIntoMap(caller_outgoing_stack, cell_id, *normalized);
      }

    }
  }
}

static std::optional<CallsiteLocalizedOutgoingFacts>
computeEntryPreludeCallOutgoingFacts(
    llvm::Module &M, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    uint64_t continuation_pc, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting) {
  auto *target_fn = M.getFunction(target_summary.function_name);
  if (!target_fn)
    return std::nullopt;
  if (depth > kMaxCallsiteLocalizationDepth)
    return std::nullopt;
  if (!target_summary.entry_va.has_value())
    return std::nullopt;
  if (!visiting.insert(target_fn).second)
    return std::nullopt;

  std::map<unsigned, VirtualValueExpr> callee_incoming;
  std::map<unsigned, VirtualValueExpr> callee_incoming_stack;
  std::map<unsigned, VirtualValueExpr> callee_incoming_args;

  for (const auto &fact : target_summary.specialization_facts)
    callee_incoming[fact.slot_id] = fact.value;
  for (const auto &fact : target_summary.specialization_stack_facts)
    callee_incoming_stack[fact.cell_id] = fact.value;

  callee_incoming_args[0] = argumentExpr(0, 64);
  if (auto it = caller_argument_map.find(0); it != caller_argument_map.end())
    callee_incoming_args[0] = it->second;
  callee_incoming_args[1] = constantExpr(*target_summary.entry_va, 64);
  if (auto it = caller_argument_map.find(2);
      it != caller_argument_map.end() &&
      isBoundedArgumentFactExpr(it->second)) {
    callee_incoming_args[2] = it->second;
  } else {
    callee_incoming_args[2] = argumentExpr(2, 64);
  }

  for (unsigned slot_id : target_summary.live_in_slot_ids) {
    auto value_it = caller_incoming.find(slot_id);
    if (value_it == caller_incoming.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming, slot_id, value_it->second);
  }
  for (unsigned cell_id : target_summary.live_in_stack_cell_ids) {
    auto value_it = caller_incoming_stack.find(cell_id);
    if (value_it == caller_incoming_stack.end() ||
        !isGloballyMergeableStateFactExpr(
            value_it->second, /*allow_arguments=*/false)) {
      continue;
    }
    mergeFactIntoMap(callee_incoming_stack, cell_id, value_it->second);
  }

  seedCallContinuationStackCell(M, continuation_pc, stack_cell_info,
                                callee_incoming_stack);

  CallsiteLocalizedOutgoingFacts localized;
  if (canComputeLocalizedSingleBlockOutgoingFacts(*target_fn, target_summary)) {
    if (auto leaf_localized = computeLocalizedSingleBlockOutgoingFacts(
            *target_fn, model, target_summary, slot_ids, stack_cell_ids,
            callee_incoming, callee_incoming_stack, callee_incoming_args,
            handler_index, outgoing_maps, outgoing_stack_maps, depth, visiting,
            nullptr, nullptr, &caller_incoming)) {
      visiting.erase(target_fn);
      return leaf_localized;
    }
  }

  for (const auto &fact : computeOutgoingFacts(target_summary, callee_incoming,
                                               callee_incoming_stack,
                                               callee_incoming_args)) {
    localized.outgoing_slots.emplace(fact.slot_id, fact.value);
  }
  for (const auto &fact :
       computeOutgoingStackFacts(target_summary, callee_incoming,
                                 callee_incoming_stack, callee_incoming_args)) {
    localized.outgoing_stack.emplace(fact.cell_id, fact.value);
  }

  if (!target_summary.direct_callees.empty()) {
    applyDirectCalleeEffectsImpl(
        *target_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming_args, localized.outgoing_slots, localized.outgoing_stack,
        slot_ids, slot_info, stack_cell_ids, stack_cell_info, M.getDataLayout(),
        depth, visiting);
  }
  if (!target_summary.callsites.empty()) {
    applyLocalizedCallsiteReturnEffects(
        *target_fn, model, target_summary, slot_info, stack_cell_info, slot_ids,
        stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
        callee_incoming, callee_incoming_stack, callee_incoming_args,
        localized.outgoing_slots, localized.outgoing_stack, depth, visiting);
  }
  if (!target_summary.direct_callees.empty() || !target_summary.callsites.empty()) {
    const auto snapshot_slots = localized.outgoing_slots;
    const auto snapshot_stack = localized.outgoing_stack;
    for (auto &[slot_id, value] : localized.outgoing_slots) {
      (void) slot_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
    for (auto &[cell_id, value] : localized.outgoing_stack) {
      (void) cell_id;
      value = specializeExpr(value, snapshot_slots, &snapshot_stack,
                             &callee_incoming_args);
    }
  }

  localized.outgoing_stack =
      rebaseOutgoingStackFacts(model, localized.outgoing_slots,
                               localized.outgoing_stack);
  visiting.erase(target_fn);
  return localized;
}

static std::optional<unsigned> lookupMappedCallerSlotId(
    llvm::CallBase &call, const VirtualStateSlotInfo &callee_slot,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl) {
  if (auto arg_index = parseArgumentBaseName(callee_slot.base_name);
      arg_index && *arg_index < call.arg_size()) {
    auto actual_slot =
        extractStateSlotSummary(call.getArgOperand(*arg_index),
                                callee_slot.width, dl);
    if (!actual_slot)
      return std::nullopt;

    VirtualStateSlotSummary mapped_slot = *actual_slot;
    mapped_slot.offset += callee_slot.offset;
    mapped_slot.width = callee_slot.width;

    auto it = slot_ids.find(slotKeyForSummary(mapped_slot));
    if (it == slot_ids.end())
      return std::nullopt;
    return it->second;
  }

  if (callee_slot.from_alloca) {
    return lookupMappedCallerSlotIdByPointerArgs(
        call, callee_slot.base_name, callee_slot.offset, callee_slot.width,
        slot_ids, dl);
  }

  return std::nullopt;
}

static std::optional<unsigned> lookupSlotIdForSummary(
    const VirtualStateSlotSummary &summary,
    const std::map<SlotKey, unsigned> &slot_ids) {
  auto it = slot_ids.find(slotKeyForSummary(summary));
  if (it != slot_ids.end())
    return it->second;

  it = llvm::find_if(slot_ids, [&](const auto &entry) {
    return entry.first.base_name == summary.base_name &&
           entry.first.offset == summary.offset &&
           entry.first.from_argument == summary.from_argument &&
           entry.first.from_alloca == summary.from_alloca;
  });
  if (it == slot_ids.end())
    return std::nullopt;
  return it->second;
}

static std::optional<VirtualStateSlotSummary> extractStateSlotSummaryFromExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info) {
  if (expr.kind != VirtualExprKind::kStateSlot)
    if (expr.kind != VirtualExprKind::kArgument || !expr.argument_index.has_value())
      return std::nullopt;

  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value()) {
    auto it = slot_info.find(*expr.slot_id);
    if (it != slot_info.end()) {
      VirtualStateSlotSummary summary;
      summary.base_name = it->second->base_name;
      summary.offset = it->second->offset;
      summary.width = it->second->width;
      summary.from_argument = it->second->from_argument;
      summary.from_alloca = it->second->from_alloca;
      return summary;
    }
  }

  VirtualStateSlotSummary summary;
  summary.width = exprByteWidth(expr);
  if (expr.kind == VirtualExprKind::kArgument) {
    summary.base_name = "arg" + std::to_string(*expr.argument_index);
    summary.offset = 0;
    summary.from_argument = true;
    summary.from_alloca = false;
  } else {
    if (!expr.state_base_name || !expr.state_offset)
      return std::nullopt;
    summary.base_name = *expr.state_base_name;
    summary.offset = *expr.state_offset;
    summary.from_argument = parseArgumentBaseName(summary.base_name).has_value();
    summary.from_alloca = !summary.from_argument;
  }
  return summary;
}

static std::optional<unsigned> lookupMappedCallerStackCellId(
    llvm::CallBase &call, const VirtualStackCellInfo &callee_cell,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  if (callee_cell.base_from_argument) {
    if (auto arg_index = parseArgumentBaseName(callee_cell.base_name);
        arg_index && *arg_index < call.arg_size()) {
      auto actual_expr = summarizeValueExpr(call.getArgOperand(*arg_index), dl);
      if (auto actual_cell =
              extractStackCellSummaryFromExpr(actual_expr, callee_cell.width)) {
        VirtualStackCellSummary mapped_cell = *actual_cell;
        mapped_cell.offset += callee_cell.cell_offset;
        mapped_cell.width = callee_cell.width;
        if (auto mapped_cell_id =
                lookupStackCellIdForSummary(mapped_cell, stack_cell_ids)) {
          return mapped_cell_id;
        }
      }
    }
  }

  if (callee_cell.base_from_alloca) {
    if (auto mapped =
            lookupMappedCallerStackCellIdByPointerArgs(
                call, callee_cell.base_name, callee_cell.base_offset,
                callee_cell.base_width, callee_cell.cell_offset,
                callee_cell.width, slot_ids, stack_cell_ids, dl)) {
      return mapped;
    }
  }

  VirtualStateSlotInfo base_slot_info{callee_cell.base_slot_id,
                                      callee_cell.base_name,
                                      callee_cell.base_offset,
                                      callee_cell.base_width,
                                      callee_cell.base_from_argument,
                                      callee_cell.base_from_alloca,
                                      {}};
  auto mapped_base_slot =
      lookupMappedCallerSlotId(call, base_slot_info, slot_ids, dl);
  if (!mapped_base_slot)
    return std::nullopt;

  auto base_slot_it = std::find_if(
      slot_ids.begin(), slot_ids.end(),
      [&](const auto &entry) { return entry.second == *mapped_base_slot; });
  if (base_slot_it == slot_ids.end())
    return std::nullopt;

  auto it = stack_cell_ids.find(
      StackCellKey{base_slot_it->first, callee_cell.cell_offset, callee_cell.width});
  if (it != stack_cell_ids.end())
    return it->second;

  it = llvm::find_if(stack_cell_ids, [&](const auto &entry) {
    return entry.first.base_slot.tie() == base_slot_it->first.tie() &&
           entry.first.cell_offset == callee_cell.cell_offset;
  });
  if (it != stack_cell_ids.end())
    return it->second;

  return findEquivalentArgumentStackCellId(
      base_slot_it->first.offset, base_slot_it->first.width,
      base_slot_it->first.from_argument, base_slot_it->first.from_alloca,
      callee_cell.cell_offset, callee_cell.width, stack_cell_ids);
}

static std::optional<unsigned> lookupStackCellIdForSummary(
    const VirtualStackCellSummary &summary,
    const std::map<StackCellKey, unsigned> &stack_cell_ids) {
  auto it = stack_cell_ids.find(stackCellKeyForSummary(summary));
  if (it != stack_cell_ids.end())
    return it->second;

  it = llvm::find_if(stack_cell_ids, [&](const auto &entry) {
    return entry.first.base_slot.base_name == summary.base_name &&
           entry.first.base_slot.offset == summary.base_offset &&
           entry.first.base_slot.from_argument == summary.base_from_argument &&
           entry.first.base_slot.from_alloca == summary.base_from_alloca &&
           entry.first.cell_offset == summary.offset;
  });
  if (it != stack_cell_ids.end())
    return it->second;

  return findEquivalentArgumentStackCellId(
      summary.base_offset, summary.base_width, summary.base_from_argument,
      summary.base_from_alloca, summary.offset, summary.width, stack_cell_ids);
}

static std::optional<VirtualValueExpr> remapStateSlotExprByShape(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl) {
  if (expr.kind != VirtualExprKind::kStateSlot || !expr.state_base_name ||
      !expr.state_offset) {
    return std::nullopt;
  }

  auto arg_index = parseArgumentBaseName(*expr.state_base_name);
  VirtualStateSlotSummary remapped_slot;
  if (arg_index && *arg_index < call.arg_size()) {
    if (auto actual_slot = extractStateSlotSummary(
            call.getArgOperand(*arg_index), exprByteWidth(expr), dl)) {
      remapped_slot = *actual_slot;
    } else {
      return std::nullopt;
    }
  } else {
    auto mapped_slot_id = lookupMappedCallerSlotIdByPointerArgs(
        call, *expr.state_base_name, *expr.state_offset, exprByteWidth(expr),
        slot_ids, dl);
    if (!mapped_slot_id)
      return std::nullopt;
    const auto &mapped_info = *slot_info.at(*mapped_slot_id);
    VirtualValueExpr mapped = expr;
    mapped.slot_id = mapped_slot_id;
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.offset;
    mapped.bit_width = mapped_info.width * 8;
    return mapped;
  }

  remapped_slot.offset += *expr.state_offset;
  remapped_slot.width = exprByteWidth(expr);

  auto mapped_slot_id = lookupSlotIdForSummary(remapped_slot, slot_ids);
  VirtualValueExpr mapped = expr;
  mapped.slot_id = mapped_slot_id;
  if (mapped_slot_id) {
    const auto &mapped_info = *slot_info.at(*mapped_slot_id);
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.offset;
    mapped.bit_width = mapped_info.width * 8;
  } else {
    mapped.state_base_name = remapped_slot.base_name;
    mapped.state_offset = remapped_slot.offset;
    mapped.bit_width = remapped_slot.width * 8;
  }
  return mapped;
}

static std::optional<VirtualValueExpr> remapStackCellExprByShape(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  if (expr.kind != VirtualExprKind::kStackCell || !expr.state_base_name ||
      !expr.state_offset || !expr.stack_offset) {
    return std::nullopt;
  }

  VirtualStackCellSummary remapped_cell;
  if (auto arg_index = parseArgumentBaseName(*expr.state_base_name);
      arg_index && *arg_index < call.arg_size()) {
    auto *actual_arg = call.getArgOperand(*arg_index);
    unsigned base_width =
        std::max(1u, getValueBitWidth(actual_arg, dl) / 8u);
    if (auto actual_slot =
            extractStateSlotSummary(actual_arg, base_width, dl)) {
      remapped_cell.base_name = actual_slot->base_name;
      remapped_cell.base_offset = actual_slot->offset + *expr.state_offset;
      remapped_cell.base_width = actual_slot->width;
      remapped_cell.base_from_argument = actual_slot->from_argument;
      remapped_cell.base_from_alloca = actual_slot->from_alloca;
      remapped_cell.offset = *expr.stack_offset;
      remapped_cell.width = exprByteWidth(expr);
    } else {
      auto actual_expr = summarizeValueExpr(actual_arg, dl);
      annotateExprSlots(actual_expr, slot_ids);
      annotateExprStackCells(actual_expr, stack_cell_ids, slot_ids);
      if (auto actual_cell =
              extractStackCellSummaryFromExpr(actual_expr, exprByteWidth(expr))) {
        remapped_cell.base_name = actual_cell->base_name;
        remapped_cell.base_offset = actual_cell->base_offset + *expr.state_offset;
        remapped_cell.base_width = actual_cell->base_width;
        remapped_cell.base_from_argument = actual_cell->base_from_argument;
        remapped_cell.base_from_alloca = actual_cell->base_from_alloca;
        remapped_cell.offset = actual_cell->offset + *expr.stack_offset;
        remapped_cell.width = exprByteWidth(expr);
      } else {
        return std::nullopt;
      }
    }
  } else {
    auto mapped_cell_id = lookupMappedCallerStackCellIdByPointerArgs(
        call, *expr.state_base_name, *expr.state_offset,
        std::max(1u, expr.bit_width / 8u), *expr.stack_offset,
        exprByteWidth(expr), slot_ids, stack_cell_ids, dl);
    if (!mapped_cell_id)
      return std::nullopt;
    const auto &mapped_info = *stack_cell_info.at(*mapped_cell_id);
    VirtualValueExpr mapped = expr;
    mapped.stack_cell_id = mapped_cell_id;
    mapped.slot_id = mapped_info.base_slot_id;
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.base_offset;
    mapped.stack_offset = mapped_info.cell_offset;
    mapped.bit_width = mapped_info.width * 8;
    return mapped;
  }

  auto mapped_cell_id = lookupStackCellIdForSummary(remapped_cell, stack_cell_ids);
  VirtualValueExpr mapped = expr;
  mapped.stack_cell_id = mapped_cell_id;
  if (mapped_cell_id) {
    const auto &mapped_info = *stack_cell_info.at(*mapped_cell_id);
    mapped.slot_id = mapped_info.base_slot_id;
    mapped.state_base_name = mapped_info.base_name;
    mapped.state_offset = mapped_info.base_offset;
    mapped.stack_offset = mapped_info.cell_offset;
    mapped.bit_width = mapped_info.width * 8;
  } else {
    VirtualStateSlotSummary base_slot;
    base_slot.base_name = remapped_cell.base_name;
    base_slot.offset = remapped_cell.base_offset;
    base_slot.width = remapped_cell.base_width;
    base_slot.from_argument = remapped_cell.base_from_argument;
    base_slot.from_alloca = remapped_cell.base_from_alloca;
    mapped.slot_id = lookupSlotIdForSummary(base_slot, slot_ids);
    mapped.state_base_name = remapped_cell.base_name;
    mapped.state_offset = remapped_cell.base_offset;
    mapped.stack_offset = remapped_cell.offset;
    mapped.bit_width = remapped_cell.width * 8;
  }
  return mapped;
}

static bool containsInvalidCallerArgumentRelativeState(
    const VirtualValueExpr &expr, const llvm::Function &caller_fn) {
  if ((expr.kind == VirtualExprKind::kStateSlot ||
       expr.kind == VirtualExprKind::kStackCell) &&
      expr.state_base_name.has_value()) {
    if (auto arg_index = parseArgumentBaseName(*expr.state_base_name);
        !arg_index || *arg_index >= caller_fn.arg_size() ||
        !caller_fn.getArg(*arg_index)->getType()->isPointerTy()) {
      if (!functionHasAllocaNamed(caller_fn, *expr.state_base_name))
        return true;
    }
  }

  return llvm::any_of(expr.operands, [&](const VirtualValueExpr &operand) {
    return containsInvalidCallerArgumentRelativeState(operand, caller_fn);
  });
}

static VirtualValueExpr remapCalleeExprToCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl) {
  if (expr.kind == VirtualExprKind::kArgument && expr.argument_index.has_value() &&
      *expr.argument_index < call.arg_size()) {
    auto actual_expr =
        summarizeValueExpr(call.getArgOperand(*expr.argument_index), dl);
    annotateExprSlots(actual_expr, slot_ids);
    annotateExprStackCells(actual_expr, stack_cell_ids, slot_ids);
    return actual_expr;
  }

  if (expr.kind == VirtualExprKind::kStateSlot && expr.slot_id.has_value()) {
    auto info_it = slot_info.find(*expr.slot_id);
    if (info_it != slot_info.end()) {
      if (auto mapped_slot =
              lookupMappedCallerSlotId(call, *info_it->second, slot_ids, dl)) {
        VirtualValueExpr mapped = expr;
        mapped.slot_id = *mapped_slot;
        const auto &mapped_info = *slot_info.at(*mapped_slot);
        mapped.state_base_name = mapped_info.base_name;
        mapped.state_offset = mapped_info.offset;
        mapped.bit_width = mapped_info.width * 8;
        return mapped;
      }
    }
  }
  if (expr.kind == VirtualExprKind::kStateSlot) {
    if (auto mapped = remapStateSlotExprByShape(expr, call, slot_info, slot_ids,
                                                dl)) {
      return *mapped;
    }
  }

  if (expr.kind == VirtualExprKind::kStackCell && expr.stack_cell_id.has_value()) {
    auto info_it = stack_cell_info.find(*expr.stack_cell_id);
    if (info_it != stack_cell_info.end()) {
      if (auto mapped_cell = lookupMappedCallerStackCellId(
              call, *info_it->second, slot_ids, stack_cell_ids, dl)) {
        VirtualValueExpr mapped = expr;
        mapped.stack_cell_id = *mapped_cell;
        const auto &mapped_info = *stack_cell_info.at(*mapped_cell);
        mapped.slot_id = mapped_info.base_slot_id;
        mapped.state_base_name = mapped_info.base_name;
        mapped.state_offset = mapped_info.base_offset;
        mapped.stack_offset = mapped_info.cell_offset;
        mapped.bit_width = mapped_info.width * 8;
        return mapped;
      }
    }
  }
  if (expr.kind == VirtualExprKind::kStackCell) {
    if (auto mapped = remapStackCellExprByShape(expr, call, slot_info,
                                                stack_cell_info, slot_ids,
                                                stack_cell_ids, dl)) {
      return *mapped;
    }
  }

  VirtualValueExpr remapped = expr;
  remapped.operands.clear();
  for (const auto &operand : expr.operands)
    remapped.operands.push_back(remapCalleeExprToCaller(
        operand, call, slot_info, stack_cell_info, slot_ids, stack_cell_ids, dl));
  return remapped;
}

static std::optional<VirtualValueExpr> normalizeImportedExprForCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  auto remapped = remapCalleeExprToCaller(expr, call, slot_info, stack_cell_info,
                                          slot_ids, stack_cell_ids, dl);
  annotateExprSlots(remapped, slot_ids);
  annotateExprStackCells(remapped, stack_cell_ids, slot_ids);

  auto specialized = specializeExpr(remapped, caller_outgoing,
                                    &caller_outgoing_stack,
                                    &caller_argument_map);
  annotateExprSlots(specialized, slot_ids);
  annotateExprStackCells(specialized, stack_cell_ids, slot_ids);

  if (containsInvalidCallerArgumentRelativeState(
          specialized, *call.getFunction())) {
    vmModelImportDebugLog("unmapped-import call=" +
                          call.getCalledFunction()->getName().str() +
                          " expr=" + renderVirtualValueExpr(expr) +
                          " remapped=" + renderVirtualValueExpr(remapped) +
                          " specialized=" +
                          renderVirtualValueExpr(specialized));
    return std::nullopt;
  }

  if ((isUnknownLikeExpr(specialized) ||
       !isBoundedStateProvenanceExpr(specialized)) &&
      isBoundedStateProvenanceExpr(remapped)) {
    return remapped;
  }

  return specialized;
}

static std::optional<VirtualValueExpr> normalizeLocalizedExprForCaller(
    const VirtualValueExpr &expr, const llvm::Function &caller_fn,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map) {
  (void) caller_outgoing;
  (void) caller_outgoing_stack;
  (void) caller_argument_map;

  VirtualValueExpr normalized = expr;
  annotateExprSlots(normalized, slot_ids);
  annotateExprStackCells(normalized, stack_cell_ids, slot_ids);
  if (containsInvalidCallerArgumentRelativeState(normalized, caller_fn))
    return std::nullopt;
  return normalized;
}

static void applyDirectCalleeEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack) {
  const auto slot_ids = buildSlotIdMap(model);
  const auto slot_info = buildSlotInfoMap(model);
  const auto stack_cell_ids = buildStackCellIdMap(model);
  const auto stack_cell_info = buildStackCellInfoMap(model);
  const auto &dl = caller_fn.getParent()->getDataLayout();
  llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
  visiting.insert(&caller_fn);
  applyDirectCalleeEffectsImpl(
      caller_fn, model, handler_index, outgoing_maps, outgoing_stack_maps,
      caller_argument_map, caller_outgoing, caller_outgoing_stack, slot_ids,
      slot_info, stack_cell_ids, stack_cell_info, dl, /*depth=*/0, visiting);
}

static void canonicalizeVirtualState(VirtualMachineModel &model) {
  auto &slots = model.mutableSlots();
  auto &stack_cells = model.mutableStackCells();
  auto &handlers = model.mutableHandlers();
  std::map<SlotKey, unsigned> slot_ids;
  std::map<StackCellKey, unsigned> stack_cell_ids;
  unsigned next_id = 0;
  unsigned next_stack_cell_id = 0;

  auto intern_slot = [&](VirtualStateSlotSummary &slot,
                         llvm::StringRef handler_name) {
    auto key = slotKeyForSummary(slot);
    auto it = slot_ids.find(key);
    if (it == slot_ids.end()) {
      unsigned id = next_id++;
      slot_ids.emplace(key, id);
      slots.push_back(VirtualStateSlotInfo{id, slot.base_name, slot.offset,
                                           slot.width, slot.from_argument,
                                           slot.from_alloca, {}});
      it = slot_ids.find(key);
    }
    slot.canonical_id = it->second;
    auto &info = slots[it->second];
    if (std::find(info.handler_names.begin(), info.handler_names.end(),
                  handler_name.str()) == info.handler_names.end()) {
      info.handler_names.push_back(handler_name.str());
    }
  };

  auto intern_stack_cell = [&](VirtualStackCellSummary &cell,
                               llvm::StringRef handler_name) {
    VirtualStateSlotSummary base_slot;
    base_slot.base_name = cell.base_name;
    base_slot.offset = cell.base_offset;
    base_slot.width = cell.base_width;
    base_slot.from_argument = cell.base_from_argument;
    base_slot.from_alloca = cell.base_from_alloca;
    intern_slot(base_slot, handler_name);
    cell.canonical_base_slot_id = base_slot.canonical_id;

    auto intern_cell_info = [&](VirtualStackCellSummary &summary) {
      auto key = stackCellKeyForSummary(summary);
      auto it = stack_cell_ids.find(key);
      if (it == stack_cell_ids.end()) {
        unsigned id = next_stack_cell_id++;
        stack_cell_ids.emplace(key, id);
        stack_cells.push_back(VirtualStackCellInfo{
            id,
            *summary.canonical_base_slot_id,
            summary.base_name,
            summary.base_offset,
            summary.base_width,
            summary.offset,
            summary.width,
            summary.base_from_argument,
            summary.base_from_alloca,
            {},
        });
        it = stack_cell_ids.find(key);
      }
      auto &info = stack_cells[it->second];
      if (std::find(info.handler_names.begin(), info.handler_names.end(),
                    handler_name.str()) == info.handler_names.end()) {
        info.handler_names.push_back(handler_name.str());
      }
      return it;
    };

    if (cell.offset != 0) {
      VirtualStackCellSummary zero_cell = cell;
      zero_cell.offset = 0;
      zero_cell.canonical_id.reset();
      zero_cell.canonical_base_slot_id = cell.canonical_base_slot_id;
      intern_cell_info(zero_cell);
    }

    auto it = intern_cell_info(cell);
    cell.canonical_id = it->second;
  };

  auto intern_expr_slots = [&](const VirtualValueExpr &expr,
                               llvm::StringRef handler_name) {
    std::vector<VirtualStateSlotSummary> referenced_slots;
    collectExprReferencedStateSlots(expr, referenced_slots);
    for (auto &slot : referenced_slots)
      intern_slot(slot, handler_name);
  };

  for (auto &summary : handlers) {
    for (auto &slot : summary.state_slots)
      intern_slot(slot, summary.function_name);
    for (auto &transfer : summary.state_transfers)
      intern_slot(transfer.target_slot, summary.function_name);
    for (auto &cell : summary.stack_cells)
      intern_stack_cell(cell, summary.function_name);
    for (auto &transfer : summary.stack_transfers)
      intern_stack_cell(transfer.target_cell, summary.function_name);
    for (const auto &dispatch : summary.dispatches)
      intern_expr_slots(dispatch.target, summary.function_name);
    for (const auto &callsite : summary.callsites)
      intern_expr_slots(callsite.target, summary.function_name);
    for (const auto &transfer : summary.state_transfers)
      intern_expr_slots(transfer.value, summary.function_name);
    for (const auto &transfer : summary.stack_transfers)
      intern_expr_slots(transfer.value, summary.function_name);
    for (const auto &fact : summary.specialization_facts)
      intern_expr_slots(fact.value, summary.function_name);
    for (const auto &fact : summary.specialization_stack_facts)
      intern_expr_slots(fact.value, summary.function_name);
    for (const auto &fact : summary.incoming_argument_facts)
      intern_expr_slots(fact.value, summary.function_name);
  }

  for (auto &summary : handlers) {
    for (auto &dispatch : summary.dispatches)
      annotateExprSlots(dispatch.target, slot_ids);
    for (auto &dispatch : summary.dispatches)
      annotateExprStackCells(dispatch.target, stack_cell_ids, slot_ids);
    for (auto &callsite : summary.callsites)
      annotateExprSlots(callsite.target, slot_ids);
    for (auto &callsite : summary.callsites)
      annotateExprStackCells(callsite.target, stack_cell_ids, slot_ids);
    for (auto &transfer : summary.state_transfers)
      annotateExprSlots(transfer.value, slot_ids);
    for (auto &transfer : summary.state_transfers)
      annotateExprStackCells(transfer.value, stack_cell_ids, slot_ids);
    for (auto &transfer : summary.stack_transfers)
      annotateExprSlots(transfer.value, slot_ids);
    for (auto &transfer : summary.stack_transfers)
      annotateExprStackCells(transfer.value, stack_cell_ids, slot_ids);

    std::set<unsigned> live_in_ids;
    std::set<unsigned> written_ids;
    std::set<unsigned> live_in_stack_ids;
    std::set<unsigned> written_stack_ids;
    for (const auto &slot : summary.state_slots) {
      if (!slot.canonical_id.has_value())
        continue;
      if (slot.loads != 0)
        live_in_ids.insert(*slot.canonical_id);
      if (slot.stores != 0)
        written_ids.insert(*slot.canonical_id);
    }
    for (const auto &cell : summary.stack_cells) {
      if (!cell.canonical_id.has_value())
        continue;
      if (cell.loads != 0)
        live_in_stack_ids.insert(*cell.canonical_id);
      if (cell.stores != 0)
        written_stack_ids.insert(*cell.canonical_id);
      if (cell.canonical_base_slot_id.has_value())
        live_in_ids.insert(*cell.canonical_base_slot_id);
    }
    for (const auto &dispatch : summary.dispatches)
      collectExprSlotIds(dispatch.target, live_in_ids);
    for (const auto &dispatch : summary.dispatches)
      collectExprStackCellIds(dispatch.target, live_in_stack_ids);
    for (const auto &callsite : summary.callsites)
      collectExprSlotIds(callsite.target, live_in_ids);
    for (const auto &callsite : summary.callsites)
      collectExprStackCellIds(callsite.target, live_in_stack_ids);
    for (const auto &transfer : summary.state_transfers) {
      if (transfer.target_slot.canonical_id.has_value())
        written_ids.insert(*transfer.target_slot.canonical_id);
      collectExprSlotIds(transfer.value, live_in_ids);
      collectExprStackCellIds(transfer.value, live_in_stack_ids);
    }
    for (const auto &transfer : summary.stack_transfers) {
      if (transfer.target_cell.canonical_id.has_value())
        written_stack_ids.insert(*transfer.target_cell.canonical_id);
      if (transfer.target_cell.canonical_base_slot_id.has_value())
        live_in_ids.insert(*transfer.target_cell.canonical_base_slot_id);
      collectExprSlotIds(transfer.value, live_in_ids);
      collectExprStackCellIds(transfer.value, live_in_stack_ids);
    }
    summary.live_in_slot_ids.assign(live_in_ids.begin(), live_in_ids.end());
    summary.written_slot_ids.assign(written_ids.begin(), written_ids.end());
    summary.live_in_stack_cell_ids.assign(live_in_stack_ids.begin(),
                                          live_in_stack_ids.end());
    summary.written_stack_cell_ids.assign(written_stack_ids.begin(),
                                          written_stack_ids.end());
  }
}

static void propagateVirtualStateFacts(llvm::Module &M,
                                       VirtualMachineModel &model,
                                       const BinaryMemoryMap &binary_memory) {
  constexpr unsigned kMaxTrackedStackCells = 32;

  auto &handlers = model.mutableHandlers();
  const auto slot_ids = buildSlotIdMap(model);
  const auto slot_info = buildSlotInfoMap(model);
  const auto stack_cell_ids = buildStackCellIdMap(model);
  const auto stack_cell_info = buildStackCellInfoMap(model);
  std::map<std::string, size_t> handler_index;
  for (size_t i = 0; i < handlers.size(); ++i)
    handler_index.emplace(handlers[i].function_name, i);

  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_argument_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> incoming_stack_maps(
      handlers.size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_stack_maps(
      handlers.size());
  std::vector<std::set<unsigned>> forced_incoming_slots(handlers.size());
  std::vector<std::set<unsigned>> forced_incoming_stack_cells(handlers.size());

  for (size_t i = 0; i < handlers.size(); ++i) {
    for (const auto &fact : handlers[i].specialization_facts) {
      incoming_maps[i][fact.slot_id] = fact.value;
      forced_incoming_slots[i].insert(fact.slot_id);
    }
    for (const auto &fact : handlers[i].specialization_stack_facts) {
      incoming_stack_maps[i][fact.cell_id] = fact.value;
      forced_incoming_stack_cells[i].insert(fact.cell_id);
    }
    if (handlers[i].entry_va.has_value()) {
      incoming_argument_maps[i][1] =
          constantExpr(*handlers[i].entry_va, /*bits=*/64);
    }
  }

  bool changed = true;
  unsigned iterations = 0;
  while (changed && iterations++ < 16) {
    changed = false;

    for (size_t i = 0; i < handlers.size(); ++i) {
      std::map<unsigned, VirtualValueExpr> outgoing_map;
      std::map<unsigned, VirtualValueExpr> outgoing_stack_map;
      bool used_localized = false;
      if (auto *caller_fn = M.getFunction(handlers[i].function_name)) {
        if (!handlers[i].direct_callees.empty() &&
            canComputeLocalizedSingleBlockOutgoingFacts(*caller_fn,
                                                       handlers[i])) {
          llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
          visiting.insert(caller_fn);
          if (auto localized = computeLocalizedSingleBlockOutgoingFacts(
                  *caller_fn, model, handlers[i], slot_ids, stack_cell_ids,
                  incoming_maps[i], incoming_stack_maps[i],
                  incoming_argument_maps[i], handler_index, outgoing_maps,
                  outgoing_stack_maps, /*depth=*/0, visiting)) {
            llvm::SmallDenseSet<unsigned, 16> written_slots(
                handlers[i].written_slot_ids.begin(),
                handlers[i].written_slot_ids.end());
            for (const auto &[slot_id, value] : localized->outgoing_slots) {
              if (!written_slots.empty() && !written_slots.count(slot_id))
                continue;
              outgoing_map.emplace(slot_id, value);
            }
            auto written_stack_cells = rebaseWrittenStackCellIds(
                model, localized->outgoing_slots,
                handlers[i].written_stack_cell_ids);
            for (const auto &[cell_id, value] : localized->outgoing_stack) {
              if (!written_stack_cells.empty() &&
                  !written_stack_cells.count(cell_id)) {
                continue;
              }
              outgoing_stack_map.emplace(cell_id, value);
            }
            used_localized = true;
          }
        }
        if (!used_localized) {
          auto new_outgoing =
              computeOutgoingFacts(handlers[i], incoming_maps[i],
                                   incoming_stack_maps[i],
                                   incoming_argument_maps[i]);
          auto new_outgoing_stack = computeOutgoingStackFacts(
              handlers[i], incoming_maps[i], incoming_stack_maps[i],
              incoming_argument_maps[i]);
          for (const auto &fact : new_outgoing)
            outgoing_map[fact.slot_id] = fact.value;
          for (const auto &fact : new_outgoing_stack)
            outgoing_stack_map[fact.cell_id] = fact.value;
          applyDirectCalleeEffects(*caller_fn, model, handler_index,
                                   outgoing_maps, outgoing_stack_maps,
                                   incoming_argument_maps[i], outgoing_map,
                                   outgoing_stack_map);
        }
      } else {
        auto new_outgoing =
            computeOutgoingFacts(handlers[i], incoming_maps[i],
                                 incoming_stack_maps[i],
                                 incoming_argument_maps[i]);
        auto new_outgoing_stack = computeOutgoingStackFacts(
            handlers[i], incoming_maps[i], incoming_stack_maps[i],
            incoming_argument_maps[i]);
        for (const auto &fact : new_outgoing)
          outgoing_map[fact.slot_id] = fact.value;
        for (const auto &fact : new_outgoing_stack)
          outgoing_stack_map[fact.cell_id] = fact.value;
      }
      outgoing_stack_map =
          rebaseOutgoingStackFacts(model, outgoing_map, outgoing_stack_map);
      bool budget_exceeded = outgoing_stack_map.size() > kMaxTrackedStackCells;
      if (budget_exceeded) {
        while (outgoing_stack_map.size() > kMaxTrackedStackCells)
          outgoing_stack_map.erase(std::prev(outgoing_stack_map.end()));
      }
      if (handlers[i].stack_memory_budget_exceeded != budget_exceeded) {
        handlers[i].stack_memory_budget_exceeded = budget_exceeded;
        changed = true;
      }
      if (!slotFactMapEquals(outgoing_map, outgoing_maps[i])) {
        outgoing_maps[i] = std::move(outgoing_map);
        changed = true;
      }
      if (!stackFactMapEquals(outgoing_stack_map, outgoing_stack_maps[i])) {
        outgoing_stack_maps[i] = std::move(outgoing_stack_map);
        changed = true;
      }
    }

    for (size_t i = 0; i < handlers.size(); ++i) {
      auto *caller_fn = M.getFunction(handlers[i].function_name);
      if (!caller_fn)
        continue;
      const auto &caller_outgoing = outgoing_maps[i];
      const auto &caller_outgoing_stack = outgoing_stack_maps[i];
      const auto &caller_arguments = incoming_argument_maps[i];
      const auto &dl = M.getDataLayout();

      auto merge_fact = [&](std::map<unsigned, VirtualValueExpr> &dst,
                            unsigned id, const VirtualValueExpr &value) {
        auto existing = dst.find(id);
        if (existing == dst.end()) {
          dst.emplace(id, value);
          changed = true;
          return;
        }
        if (exprEquals(existing->second, value))
          return;
        auto merged = mergeIncomingExpr(existing->second, value);
        if (merged.has_value()) {
          if (!exprEquals(existing->second, *merged)) {
            existing->second = std::move(*merged);
            changed = true;
          }
          return;
        }
        auto unknown = unknownExpr(existing->second.bit_width
                                       ? existing->second.bit_width
                                       : value.bit_width);
        if (!exprEquals(existing->second, unknown)) {
          existing->second = std::move(unknown);
          changed = true;
        }
      };

      for (auto &BB : *caller_fn) {
        for (auto &I : BB) {
          auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
          if (!call)
            continue;
          auto *callee = call->getCalledFunction();
          if (!callee)
            continue;
          auto callee_it = handler_index.find(callee->getName().str());
          if (callee_it == handler_index.end())
            continue;

          auto &callee_incoming = incoming_maps[callee_it->second];
          auto &callee_incoming_stack = incoming_stack_maps[callee_it->second];
          auto &callee_incoming_args = incoming_argument_maps[callee_it->second];
          const auto &callee_summary = handlers[callee_it->second];
          std::set<unsigned> allowed(callee_summary.live_in_slot_ids.begin(),
                                     callee_summary.live_in_slot_ids.end());
          std::set<unsigned> allowed_stack(
              callee_summary.live_in_stack_cell_ids.begin(),
              callee_summary.live_in_stack_cell_ids.end());

          for (const auto &[slot_id, value] : caller_outgoing) {
            if (!allowed.empty() && !allowed.count(slot_id))
              continue;
            if (forced_incoming_slots[callee_it->second].count(slot_id))
              continue;
            if (!isGloballyMergeableStateFactExpr(
                    value, /*allow_arguments=*/false))
              continue;
            merge_fact(callee_incoming, slot_id, value);
          }
          for (const auto &[cell_id, value] : caller_outgoing_stack) {
            if (!allowed_stack.empty() && !allowed_stack.count(cell_id))
              continue;
            if (forced_incoming_stack_cells[callee_it->second].count(cell_id))
              continue;
            if (!isGloballyMergeableStateFactExpr(
                    value, /*allow_arguments=*/false))
              continue;
            merge_fact(callee_incoming_stack, cell_id, value);
          }

          for (unsigned callee_slot_id : callee_summary.live_in_slot_ids) {
            if (forced_incoming_slots[callee_it->second].count(callee_slot_id))
              continue;
            auto info_it = slot_info.find(callee_slot_id);
            if (info_it == slot_info.end())
              continue;
            auto mapped_slot_id = lookupMappedCallerSlotId(
                *call, *info_it->second, slot_ids, dl);
            if (!mapped_slot_id)
              continue;
            auto value_it = caller_outgoing.find(*mapped_slot_id);
            if (value_it == caller_outgoing.end())
              continue;
            if (!isSimpleRemappableFactExpr(value_it->second) ||
                containsCallerLocalAllocaStateExpr(value_it->second))
              continue;
            merge_fact(callee_incoming, callee_slot_id, value_it->second);
          }

          for (unsigned callee_cell_id : callee_summary.live_in_stack_cell_ids) {
            if (forced_incoming_stack_cells[callee_it->second].count(
                    callee_cell_id)) {
              continue;
            }
            auto info_it = stack_cell_info.find(callee_cell_id);
            if (info_it == stack_cell_info.end())
              continue;
            auto mapped_cell_id = lookupMappedCallerStackCellId(
                *call, *info_it->second, slot_ids, stack_cell_ids, dl);
            if (!mapped_cell_id)
              continue;
            auto value_it = caller_outgoing_stack.find(*mapped_cell_id);
            if (value_it == caller_outgoing_stack.end())
              continue;
            if (!isSimpleRemappableFactExpr(value_it->second) ||
                containsCallerLocalAllocaStateExpr(value_it->second))
              continue;
            merge_fact(callee_incoming_stack, callee_cell_id, value_it->second);
          }

          for (unsigned arg_index = 0; arg_index < call->arg_size(); ++arg_index) {
            auto arg_expr = summarizeValueExpr(call->getArgOperand(arg_index), dl);
            annotateExprSlots(arg_expr, slot_ids);
            annotateExprStackCells(arg_expr, stack_cell_ids, slot_ids);
            auto specialized = specializeExpr(arg_expr, caller_outgoing,
                                              &caller_outgoing_stack,
                                              &caller_arguments);
            if (!isGloballyMergeableStateFactExpr(
                    specialized, /*allow_arguments=*/true))
              continue;
            merge_fact(callee_incoming_args, arg_index, specialized);
          }

          if (auto continuation_pc = inferLiftedCallContinuationPc(*call)) {
            auto sp_offset = lookupNativeStackPointerOffset(M);
            if (sp_offset.has_value()) {
              for (const auto &[callee_cell_id, cell] : stack_cell_info) {
                if (!cell->base_from_argument || cell->base_from_alloca)
                  continue;
                auto arg_index = parseArgumentBaseName(cell->base_name);
                if (!arg_index || *arg_index != 0)
                  continue;
                if (cell->base_offset != static_cast<int64_t>(*sp_offset) ||
                    cell->cell_offset != 0) {
                  continue;
                }
                vmModelImportDebugLog("seeded-call-continuation callee=" +
                                      callee->getName().str() + " cell=" +
                                      std::to_string(callee_cell_id) +
                                      " pc=0x" +
                                      llvm::utohexstr(*continuation_pc));
                merge_fact(callee_incoming_stack, callee_cell_id,
                           constantExpr(*continuation_pc, cell->width * 8));
              }
            }
          }
        }
      }

      if (handlers[i].entry_va.has_value()) {
        auto prelude =
            detectEntryPreludeDirectCall(binary_memory, *handlers[i].entry_va);
        if (prelude.has_value()) {
          if (const auto *target_summary =
                  lookupHandlerByEntryVA(model, prelude->target_pc)) {
            llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
            auto localized = computeEntryPreludeCallOutgoingFacts(
                M, model, *target_summary, slot_info, stack_cell_info, slot_ids,
                stack_cell_ids, handler_index, outgoing_maps, outgoing_stack_maps,
                incoming_maps[i], incoming_stack_maps[i],
                incoming_argument_maps[i], prelude->continuation_pc,
                /*depth=*/1, visiting);
            if (localized) {
              llvm::SmallDenseSet<unsigned, 16> written_slots(
                  target_summary->written_slot_ids.begin(),
                  target_summary->written_slot_ids.end());
              auto written_stack_cells = rebaseWrittenStackCellIds(
                  model, localized->outgoing_slots,
                  target_summary->written_stack_cell_ids);

              for (const auto &[slot_id, value] : localized->outgoing_slots) {
                if (!written_slots.empty() && !written_slots.count(slot_id))
                  continue;
                if (forced_incoming_slots[i].count(slot_id))
                  continue;
                if (!isGloballyMergeableStateFactExpr(
                        value, /*allow_arguments=*/false)) {
                  continue;
                }
                merge_fact(incoming_maps[i], slot_id, value);
              }
              for (const auto &[cell_id, value] : localized->outgoing_stack) {
                if (!written_stack_cells.empty() &&
                    !written_stack_cells.count(cell_id)) {
                  continue;
                }
                if (forced_incoming_stack_cells[i].count(cell_id))
                  continue;
                if (!isGloballyMergeableStateFactExpr(
                        value, /*allow_arguments=*/false)) {
                  continue;
                }
                merge_fact(incoming_stack_maps[i], cell_id, value);
              }
            }
          }
        }
      }
    }
  }

  for (size_t i = 0; i < handlers.size(); ++i) {
    handlers[i].incoming_argument_facts.clear();
    for (const auto &[arg_index, value] : incoming_argument_maps[i]) {
      handlers[i].incoming_argument_facts.push_back(
          VirtualArgumentFact{arg_index, value});
    }

    handlers[i].incoming_facts.clear();
    for (const auto &[slot_id, value] : incoming_maps[i])
      handlers[i].incoming_facts.push_back(VirtualSlotFact{slot_id, value});

    handlers[i].outgoing_facts.clear();
    for (const auto &[slot_id, value] : outgoing_maps[i])
      handlers[i].outgoing_facts.push_back(VirtualSlotFact{slot_id, value});

    handlers[i].incoming_stack_facts.clear();
    for (const auto &[cell_id, value] : incoming_stack_maps[i])
      handlers[i].incoming_stack_facts.push_back(VirtualStackFact{cell_id, value});

    handlers[i].outgoing_stack_facts.clear();
    for (const auto &[cell_id, value] : outgoing_stack_maps[i])
      handlers[i].outgoing_stack_facts.push_back(VirtualStackFact{cell_id, value});
  }
}

static const VirtualBoundaryInfo *lookupBoundaryByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va) {
  for (const auto &boundary : model.boundaries()) {
    if (boundary.entry_va.has_value() && *boundary.entry_va == entry_va)
      return &boundary;
  }
  return nullptr;
}

static std::optional<std::string> resolveBoundaryNameForTarget(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    uint64_t pc) {
  if (const auto *boundary = lookupBoundaryByEntryVA(model, pc))
    return normalizeBoundaryName(boundary->name);

  auto fallback_name = syntheticBoundaryName(pc);
  if (const auto *boundary = model.lookupBoundary(fallback_name))
    return normalizeBoundaryName(boundary->name);

  if (auto boundary = classifyProtectedBoundary(binary_memory, pc)) {
    if (const auto *existing =
            lookupBoundaryByEntryVA(model, boundary->entry_va)) {
      return normalizeBoundaryName(existing->name);
    }
    return syntheticBoundaryName(boundary->entry_va);
  }

  return std::nullopt;
}

struct BoundaryTargetSummary {
  std::string name;
  std::optional<uint64_t> canonical_target_va;
};

static std::optional<BoundaryTargetSummary> lookupBoundaryTargetSummary(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    uint64_t pc) {
  if (const auto *boundary = lookupBoundaryByEntryVA(model, pc)) {
    return BoundaryTargetSummary{normalizeBoundaryName(boundary->name),
                                 boundary->target_va};
  }

  auto fallback_name = syntheticBoundaryName(pc);
  if (const auto *boundary = model.lookupBoundary(fallback_name)) {
    return BoundaryTargetSummary{normalizeBoundaryName(boundary->name),
                                 boundary->target_va};
  }

  if (auto boundary = classifyProtectedBoundary(binary_memory, pc)) {
    BoundaryTargetSummary summary;
    if (const auto *existing =
            lookupBoundaryByEntryVA(model, boundary->entry_va)) {
      summary.name = normalizeBoundaryName(existing->name);
      summary.canonical_target_va = existing->target_va.has_value()
                                        ? existing->target_va
                                        : std::optional<uint64_t>(
                                              boundary->canonical_target_va);
    } else {
      summary.name = syntheticBoundaryName(boundary->entry_va);
      summary.canonical_target_va = boundary->canonical_target_va;
    }
    return summary;
  }

  return std::nullopt;
}

static std::optional<VirtualDispatchSuccessorSummary>
classifyDispatchSuccessor(const VirtualMachineModel &model,
                         const BinaryMemoryMap &binary_memory,
                         uint64_t pc) {
  if (auto boundary =
          lookupBoundaryTargetSummary(model, binary_memory, pc)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kProtectedBoundary;
    successor.target_pc = pc;
    successor.boundary_name = boundary->name;
    successor.canonical_boundary_target_va = boundary->canonical_target_va;
    return successor;
  }

  for (const auto &handler : model.handlers()) {
    if (!handler.entry_va.has_value() || *handler.entry_va != pc)
      continue;

    VirtualDispatchSuccessorSummary successor;
    llvm::StringRef handler_name(handler.function_name);
    if (handler_name.starts_with("blk_")) {
      successor.kind = VirtualSuccessorKind::kLiftedBlock;
    } else if (handler_name.starts_with("block_")) {
      successor.kind = VirtualSuccessorKind::kTraceBlock;
    } else {
      successor.kind = VirtualSuccessorKind::kLiftedHandler;
    }
    successor.target_pc = pc;
    successor.target_function_name = handler.function_name;
    return successor;
  }

  auto lifted_name = liftedFunctionName(pc);
  if (model.lookupHandler(lifted_name)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kLiftedHandler;
    successor.target_pc = pc;
    successor.target_function_name = lifted_name;
    return successor;
  }

  auto block_name = (llvm::Twine("blk_") + llvm::Twine::utohexstr(pc)).str();
  if (model.lookupHandler(block_name)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kLiftedBlock;
    successor.target_pc = pc;
    successor.target_function_name = block_name;
    return successor;
  }

  auto trace_block_name =
      (llvm::Twine("block_") + llvm::Twine::utohexstr(pc)).str();
  if (model.lookupHandler(trace_block_name)) {
    VirtualDispatchSuccessorSummary successor;
    successor.kind = VirtualSuccessorKind::kTraceBlock;
    successor.target_pc = pc;
    successor.target_function_name = trace_block_name;
    return successor;
  }

  return std::nullopt;
}

static std::map<unsigned, VirtualValueExpr> factMapFor(
    llvm::ArrayRef<VirtualSlotFact> facts) {
  std::map<unsigned, VirtualValueExpr> result;
  for (const auto &fact : facts)
    result.emplace(fact.slot_id, fact.value);
  return result;
}

static std::map<unsigned, VirtualValueExpr> stackFactMapFor(
    llvm::ArrayRef<VirtualStackFact> facts) {
  std::map<unsigned, VirtualValueExpr> result;
  for (const auto &fact : facts)
    result.emplace(fact.cell_id, fact.value);
  return result;
}

static std::map<unsigned, VirtualValueExpr> argumentFactMapFor(
    llvm::ArrayRef<VirtualArgumentFact> facts) {
  std::map<unsigned, VirtualValueExpr> result;
  for (const auto &fact : facts)
    result.emplace(fact.argument_index, fact.value);
  return result;
}

static std::vector<VirtualSlotFact> slotFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts) {
  std::vector<VirtualSlotFact> result;
  result.reserve(facts.size());
  for (const auto &[slot_id, value] : facts)
    result.push_back(VirtualSlotFact{slot_id, value});
  return result;
}

static std::vector<VirtualStackFact> stackFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts) {
  std::vector<VirtualStackFact> result;
  result.reserve(facts.size());
  for (const auto &[cell_id, value] : facts)
    result.push_back(VirtualStackFact{cell_id, value});
  return result;
}

static void summarizeDispatchSuccessors(llvm::Module &M,
                                        VirtualMachineModel &model,
                                        const BinaryMemoryMap &binary_memory) {
  auto slot_ids = buildSlotIdMap(model);
  auto stack_cell_ids = buildStackCellIdMap(model);
  auto boolean_slot_ids = buildBooleanFlagSlotIds(M, model);
  auto boolean_slot_expr_keys = buildBooleanFlagExprKeys(M, model);
  auto &handlers = model.mutableHandlers();
  for (auto &summary : handlers) {
    const auto *region = model.lookupRegionForHandler(summary.function_name);
    auto outgoing_map = factMapFor(summary.outgoing_facts);
    auto incoming_map = factMapFor(summary.incoming_facts);
    auto incoming_arg_map = argumentFactMapFor(summary.incoming_argument_facts);
    auto outgoing_stack_map = stackFactMapFor(summary.outgoing_stack_facts);
    auto incoming_stack_map = stackFactMapFor(summary.incoming_stack_facts);
    std::map<unsigned, VirtualValueExpr> region_outgoing_map;
    std::map<unsigned, VirtualValueExpr> region_incoming_map;
    std::map<unsigned, VirtualValueExpr> region_outgoing_stack_map;
    std::map<unsigned, VirtualValueExpr> region_incoming_stack_map;
    if (region) {
      region_outgoing_map = factMapFor(region->outgoing_facts);
      region_incoming_map = factMapFor(region->incoming_facts);
      region_outgoing_stack_map = stackFactMapFor(region->outgoing_stack_facts);
      region_incoming_stack_map = stackFactMapFor(region->incoming_stack_facts);
    }

    for (auto &dispatch : summary.dispatches) {
      dispatch.successors.clear();
      dispatch.unresolved_reason.clear();
      dispatch.specialized_target = dispatch.target;
      dispatch.specialized_target_source =
          VirtualDispatchResolutionSource::kDirect;

      auto note_target_expr = [&](const VirtualValueExpr &expr,
                                  VirtualDispatchResolutionSource source) {
        unsigned current_refs = countSymbolicRefs(dispatch.specialized_target);
        unsigned new_refs = countSymbolicRefs(expr);
        bool current_is_unknown = isUnknownLikeExpr(dispatch.specialized_target);
        bool new_is_unknown = isUnknownLikeExpr(expr);
        bool current_is_original =
            exprEquals(dispatch.specialized_target, dispatch.target);
        bool new_is_original = exprEquals(expr, dispatch.target);
        if (new_is_unknown && !current_is_unknown)
          return;
        if ((current_is_original && !new_is_original && !new_is_unknown) ||
            new_refs < current_refs ||
            (current_is_unknown && !new_is_unknown) ||
            (new_refs == current_refs && current_is_original &&
             !new_is_original)) {
          dispatch.specialized_target = expr;
          dispatch.specialized_target_source = source;
        }
      };

      struct ResolvedPC {
        uint64_t pc = 0;
        VirtualDispatchResolutionSource source =
            VirtualDispatchResolutionSource::kUnknown;
      };
      llvm::SmallVector<ResolvedPC, 4> resolved_pcs;
      auto append_pc = [&](uint64_t pc, VirtualDispatchResolutionSource source) {
        auto it = llvm::find_if(resolved_pcs, [&](const ResolvedPC &resolved) {
          return resolved.pc == pc;
        });
        if (it == resolved_pcs.end())
          resolved_pcs.push_back(ResolvedPC{pc, source});
      };

      auto collect_from_expr =
          [&](VirtualValueExpr expr,
              llvm::ArrayRef<VirtualSlotFact> slot_facts,
              llvm::ArrayRef<VirtualStackFact> stack_facts,
              VirtualDispatchResolutionSource source) {
        annotateExprSlots(expr, slot_ids);
        annotateExprStackCells(expr, stack_cell_ids, slot_ids);
        note_target_expr(expr, source);
        if (auto pc = evaluateVirtualExpr(expr, slot_facts, stack_facts)) {
          append_pc(*pc, source);
          return;
        }
        llvm::SmallVector<uint64_t, 4> choices;
        if (collectEvaluatedTargetChoices(expr, slot_facts, stack_facts,
                                         &boolean_slot_ids,
                                         &boolean_slot_expr_keys, choices)) {
          for (uint64_t pc : choices)
            append_pc(pc, source);
        }
      };

      collect_from_expr(dispatch.target, summary.outgoing_facts,
                        summary.outgoing_stack_facts,
                        VirtualDispatchResolutionSource::kDirect);
      if (resolved_pcs.empty()) {
        auto specialized = specializeExpr(dispatch.target, outgoing_map,
                                          &outgoing_stack_map,
                                          &incoming_arg_map);
        collect_from_expr(
            specialized, summary.outgoing_facts, summary.outgoing_stack_facts,
            exprEquals(specialized, dispatch.target)
                ? VirtualDispatchResolutionSource::kOutgoingFacts
                : VirtualDispatchResolutionSource::kHelperArgumentSpecialization);
      }
      if (resolved_pcs.empty() && region) {
        auto specialized = specializeExpr(dispatch.target, region_outgoing_map,
                                          &region_outgoing_stack_map,
                                          &incoming_arg_map);
        collect_from_expr(
            specialized, region->outgoing_facts, region->outgoing_stack_facts,
            exprEquals(specialized, dispatch.target)
                ? VirtualDispatchResolutionSource::kRegionOutgoingFacts
                : VirtualDispatchResolutionSource::kHelperArgumentSpecialization);
      }
      if (resolved_pcs.empty()) {
        collect_from_expr(
            specializeExpr(dispatch.target, incoming_map, &incoming_stack_map,
                           &incoming_arg_map),
            summary.incoming_facts, summary.incoming_stack_facts,
            VirtualDispatchResolutionSource::kIncomingFacts);
      }
      if (resolved_pcs.empty() && region) {
        collect_from_expr(
            specializeExpr(dispatch.target, region_incoming_map,
                           &region_incoming_stack_map, &incoming_arg_map),
            region->incoming_facts, region->incoming_stack_facts,
            VirtualDispatchResolutionSource::kRegionIncomingFacts);
      }

      for (const auto &resolved_pc : resolved_pcs) {
        if (auto successor =
                classifyDispatchSuccessor(model, binary_memory, resolved_pc.pc)) {
          successor->resolution_source = resolved_pc.source;
          dispatch.successors.push_back(*successor);
          continue;
        }

        VirtualDispatchSuccessorSummary successor;
        successor.kind = VirtualSuccessorKind::kUnknown;
        successor.target_pc = resolved_pc.pc;
        successor.resolution_source = resolved_pc.source;
        dispatch.successors.push_back(std::move(successor));
      }

      if (dispatch.successors.empty()) {
        if (summary.stack_memory_budget_exceeded) {
          dispatch.unresolved_reason = "stack_fact_budget_exceeded";
        } else if (containsStateSlotExpr(dispatch.specialized_target) &&
                   !isBoundedStateProvenanceExpr(dispatch.specialized_target)) {
          dispatch.unresolved_reason = "unsupported_slot_provenance_target";
        } else if (summary.has_unsupported_stack_memory ||
                   (containsStackCellExpr(dispatch.specialized_target) &&
                    !isBoundedStateProvenanceExpr(
                        dispatch.specialized_target))) {
          dispatch.unresolved_reason = "unsupported_memory_target";
        } else {
          dispatch.unresolved_reason = "dynamic_target";
        }
        continue;
      }

      bool has_unknown = std::any_of(
          dispatch.successors.begin(), dispatch.successors.end(),
          [](const VirtualDispatchSuccessorSummary &successor) {
            return successor.kind == VirtualSuccessorKind::kUnknown;
          });
      if (has_unknown)
        dispatch.unresolved_reason = "missing_lifted_target";
    }
  }
}

static void summarizeCallSites(llvm::Module &M, VirtualMachineModel &model,
                               const BinaryMemoryMap &binary_memory) {
  auto target_arch = targetArchForModule(M);
  auto slot_ids = buildSlotIdMap(model);
  auto slot_info = buildSlotInfoMap(model);
  auto stack_cell_ids = buildStackCellIdMap(model);
  auto stack_cell_info = buildStackCellInfoMap(model);
  std::map<std::string, size_t> handler_index;
  for (size_t i = 0; i < model.handlers().size(); ++i)
    handler_index.emplace(model.handlers()[i].function_name, i);

  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_maps(
      model.handlers().size());
  std::vector<std::map<unsigned, VirtualValueExpr>> outgoing_stack_maps(
      model.handlers().size());
  for (size_t i = 0; i < model.handlers().size(); ++i) {
    outgoing_maps[i] = factMapFor(model.handlers()[i].outgoing_facts);
    outgoing_stack_maps[i] = stackFactMapFor(model.handlers()[i].outgoing_stack_facts);
  }

  auto &handlers = model.mutableHandlers();
  const auto &dl = M.getDataLayout();
  for (auto &summary : handlers) {
    for (auto &callsite : summary.callsites) {
      callsite.specialized_target = callsite.target;
      callsite.specialized_target_source =
          VirtualDispatchResolutionSource::kUnknown;
      callsite.resolved_target_pc.reset();
      callsite.recovered_entry_pc.reset();
      callsite.continuation_pc.reset();
      callsite.is_executable_in_image = false;
      callsite.is_decodable_entry = false;
      callsite.target_function_name.reset();
      callsite.recovered_target_function_name.reset();
      callsite.return_slot_facts.clear();
      callsite.return_stack_facts.clear();
      callsite.unresolved_reason.clear();
    }

    auto *caller_fn = M.getFunction(summary.function_name);
    if (!caller_fn)
      continue;

    auto caller_incoming = factMapFor(summary.incoming_facts);
    auto caller_incoming_stack = stackFactMapFor(summary.incoming_stack_facts);
    auto caller_outgoing = factMapFor(summary.outgoing_facts);
    auto caller_outgoing_stack = stackFactMapFor(summary.outgoing_stack_facts);
    auto caller_argument_map = argumentFactMapFor(summary.incoming_argument_facts);
    size_t callsite_index = 0;

    for (auto &BB : *caller_fn) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || !isCallSiteHelper(*callee))
          continue;
        if (callsite_index >= summary.callsites.size())
          continue;

        auto &callsite_summary = summary.callsites[callsite_index++];
        auto local_state = computeLocalFactsBeforeCall(
            *call, dl, slot_ids, stack_cell_ids,
            caller_incoming, caller_incoming_stack, caller_argument_map);
        auto resolved = resolveCallSiteInfo(
            *call, dl, slot_ids, stack_cell_ids, local_state.slot_facts,
            local_state.stack_facts, caller_argument_map);
        if (!resolved.target_pc.has_value()) {
          auto outgoing_local_state = computeLocalFactsBeforeCall(
              *call, dl, slot_ids, stack_cell_ids, caller_outgoing,
              caller_outgoing_stack, caller_argument_map);
          auto outgoing_resolved = resolveCallSiteInfo(
              *call, dl, slot_ids, stack_cell_ids,
              outgoing_local_state.slot_facts, outgoing_local_state.stack_facts,
              caller_argument_map);
          vmModelImportDebugLog("callsite-fallback handler=" +
                                summary.function_name + " incoming=" +
                                renderVirtualValueExpr(resolved.target_expr) +
                                " outgoing=" +
                                renderVirtualValueExpr(
                                    outgoing_resolved.target_expr) +
                                " incoming_pc=" +
                                (resolved.target_pc
                                     ? ("0x" +
                                        llvm::utohexstr(*resolved.target_pc))
                                     : std::string("<none>")) +
                                " outgoing_pc=" +
                                (outgoing_resolved.target_pc
                                     ? ("0x" + llvm::utohexstr(
                                                  *outgoing_resolved.target_pc))
                                     : std::string("<none>")));
          if (outgoing_resolved.target_pc.has_value())
            resolved = std::move(outgoing_resolved);
        }

        bool target_is_executable =
            resolved.target_pc.has_value() &&
            isTargetExecutable(binary_memory, *resolved.target_pc);
        if ((!resolved.target_pc.has_value() || !target_is_executable) &&
            resolved.continuation_pc.has_value()) {
          if (auto next_pc_resolved = resolveCallSiteInfoFromOutgoingNextPc(
                  summary, callsite_summary.target, resolved.continuation_pc,
                  slot_ids)) {
            vmModelImportDebugLog(
                "callsite-nextpc-fallback handler=" + summary.function_name +
                " direct=" + renderVirtualValueExpr(callsite_summary.target) +
                " outgoing_next_pc=" +
                renderVirtualValueExpr(next_pc_resolved->target_expr) +
                " target_pc=0x" +
                llvm::utohexstr(*next_pc_resolved->target_pc));
            resolved = std::move(*next_pc_resolved);
          }
        }
        callsite_summary.specialized_target = resolved.target_expr;
        callsite_summary.specialized_target_source = resolved.target_source;
        callsite_summary.resolved_target_pc = resolved.target_pc;
        callsite_summary.continuation_pc = resolved.continuation_pc;

        if (!resolved.target_pc.has_value()) {
          callsite_summary.unresolved_reason = "call_target_unresolved";
          continue;
        }
        callsite_summary.is_executable_in_image =
            isTargetExecutable(binary_memory, *resolved.target_pc);
        if (!callsite_summary.is_executable_in_image) {
          callsite_summary.unresolved_reason = "call_target_not_executable";
          continue;
        }

        auto decodable_entry = isTargetDecodableEntry(
            binary_memory, *resolved.target_pc, target_arch);
        const auto *target_summary =
            lookupHandlerByEntryVA(model, *resolved.target_pc);
        std::optional<uint64_t> nearby_entry_pc;
        const VirtualHandlerSummary *nearby_summary = nullptr;
        if (target_summary) {
          callsite_summary.is_decodable_entry = true;
        } else if (decodable_entry.has_value()) {
          callsite_summary.is_decodable_entry = *decodable_entry;
          if (!*decodable_entry) {
            nearby_summary = findNearbyLiftedHandlerEntry(
                model, *resolved.target_pc, target_arch);
            if (nearby_summary && nearby_summary->entry_va.has_value()) {
              nearby_entry_pc = nearby_summary->entry_va;
              callsite_summary.recovered_target_function_name =
                  nearby_summary->function_name;
            } else {
              nearby_entry_pc = findNearbyExecutableEntry(
                  binary_memory, *resolved.target_pc, target_arch);
              if (nearby_entry_pc) {
                nearby_summary = lookupHandlerByEntryVA(model, *nearby_entry_pc);
                if (nearby_summary) {
                  callsite_summary.recovered_target_function_name =
                      nearby_summary->function_name;
                }
              }
            }
            callsite_summary.recovered_entry_pc = nearby_entry_pc;
          }
        }
        if (!target_summary && !nearby_summary) {
          if (nearby_entry_pc) {
            callsite_summary.unresolved_reason = "call_target_nearby_unlifted";
          } else {
            callsite_summary.unresolved_reason =
                (decodable_entry.has_value() && !*decodable_entry)
                    ? "call_target_undecodable"
                    : "call_target_unlifted";
          }
          continue;
        }

        const auto *localized_target_summary =
            target_summary ? target_summary : nearby_summary;
        if (!target_summary) {
          if (nearby_summary) {
            callsite_summary.unresolved_reason = "call_target_mid_instruction";
          }
        } else {
          callsite_summary.target_function_name = target_summary->function_name;
        }

        llvm::SmallPtrSet<const llvm::Function *, 8> visiting;
        visiting.insert(caller_fn);
        auto localized = computeResolvedCallTargetOutgoingFacts(
            *call, model, *localized_target_summary, slot_info, stack_cell_info,
            slot_ids, stack_cell_ids, dl, handler_index, outgoing_maps,
            outgoing_stack_maps, caller_outgoing, caller_outgoing_stack,
            caller_argument_map, resolved, /*depth=*/1, visiting);
        if (!localized) {
          if (callsite_summary.unresolved_reason.empty())
            callsite_summary.unresolved_reason = "call_return_unresolved";
          continue;
        }

        llvm::SmallDenseSet<unsigned, 16> written_slots(
            localized_target_summary->written_slot_ids.begin(),
            localized_target_summary->written_slot_ids.end());
        auto written_stack_cells = rebaseWrittenStackCellIds(
            model, localized->outgoing_slots,
            localized_target_summary->written_stack_cell_ids);

        for (const auto &[slot_id, value] : localized->outgoing_slots) {
          if (!written_slots.empty() && !written_slots.count(slot_id))
            continue;
          auto normalized = normalizeLocalizedExprForCaller(
              value, *caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
              caller_outgoing_stack, caller_argument_map);
          if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
              !isBoundedStateProvenanceExpr(*normalized)) {
            continue;
          }
          callsite_summary.return_slot_facts.push_back(
              VirtualSlotFact{slot_id, std::move(*normalized)});
        }
        for (const auto &[cell_id, value] : localized->outgoing_stack) {
          if (!written_stack_cells.empty() &&
              !written_stack_cells.count(cell_id)) {
            continue;
          }
          auto normalized = normalizeLocalizedExprForCaller(
              value, *caller_fn, slot_ids, stack_cell_ids, caller_outgoing,
              caller_outgoing_stack, caller_argument_map);
          if (!normalized.has_value() || isUnknownLikeExpr(*normalized) ||
              !isBoundedStateProvenanceExpr(*normalized)) {
            continue;
          }
          callsite_summary.return_stack_facts.push_back(
              VirtualStackFact{cell_id, std::move(*normalized)});
        }

        if (callsite_summary.unresolved_reason.empty() &&
            callsite_summary.continuation_pc.has_value() &&
            callsite_summary.return_slot_facts.empty() &&
            callsite_summary.return_stack_facts.empty()) {
          callsite_summary.unresolved_reason = "call_return_unresolved";
        }
      }
    }
  }
}

static void summarizeRootSlices(llvm::Module &M, VirtualMachineModel &model,
                                const BinaryMemoryMap &binary_memory) {
  auto target_arch = targetArchForModule(M);
  auto &root_slices = model.mutableRootSlices();
  root_slices.clear();

  const auto &handlers = model.handlers();
  if (handlers.empty())
    return;

  std::map<std::string, const VirtualHandlerSummary *> handler_by_name;
  std::map<uint64_t, const VirtualHandlerSummary *> handler_by_pc;
  for (const auto &handler : handlers) {
    handler_by_name.emplace(handler.function_name, &handler);
    if (handler.entry_va.has_value())
      handler_by_pc.emplace(*handler.entry_va, &handler);
  }

  auto enqueue_handler = [&](const VirtualHandlerSummary *handler,
                             std::vector<const VirtualHandlerSummary *> &queue,
                             std::set<std::string> &visited) {
    if (!handler || !visited.insert(handler->function_name).second)
      return;
    queue.push_back(handler);
  };

  auto has_lifted_direct_callee =
      [&](const VirtualHandlerSummary &handler) -> bool {
    for (const auto &callee_name : handler.direct_callees) {
      auto it = handler_by_name.find(callee_name);
      if (it == handler_by_name.end())
        continue;
      if (it->second->entry_va.has_value())
        return true;
    }
    return false;
  };

  auto exprReferencesNamedSlot =
      [&](const VirtualValueExpr &expr, llvm::StringRef slot_name,
          const auto &self) -> bool {
    if (expr.kind == VirtualExprKind::kStateSlot) {
      if (expr.state_base_name.has_value() &&
          *expr.state_base_name == slot_name) {
        return true;
      }
      if (expr.slot_id.has_value()) {
        if (const auto *slot = model.lookupSlot(*expr.slot_id);
            slot && slot->base_name == slot_name) {
          return true;
        }
      }
    }
    if (expr.kind == VirtualExprKind::kStackCell &&
        expr.state_base_name.has_value() &&
        *expr.state_base_name == slot_name) {
      return true;
    }
    for (const auto &operand : expr.operands) {
      if (self(operand, slot_name, self))
        return true;
    }
    return false;
  };

  auto has_same_handler_localized_continuation =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
    if (!callsite.continuation_pc.has_value())
      return false;
    if (!handler.dispatches.empty())
      return false;

    auto is_localized_expr = [&](const VirtualValueExpr &expr) {
      return exprReferencesNamedSlot(expr, "RETURN_PC",
                                     exprReferencesNamedSlot) ||
             (expr.kind == VirtualExprKind::kConstant &&
              expr.constant.has_value() &&
              *expr.constant == *callsite.continuation_pc);
    };

    for (const auto &fact : handler.outgoing_facts) {
      if (is_localized_expr(fact.value))
        return true;
    }
    for (const auto &fact : handler.outgoing_stack_facts) {
      if (is_localized_expr(fact.value))
        return true;
    }
    return false;
  };

  auto is_semantically_localized_callsite =
      [&](const VirtualHandlerSummary &handler,
          const VirtualCallSiteSummary &callsite) -> bool {
    if (!callsite.continuation_pc.has_value())
      return false;
    if (!has_lifted_direct_callee(handler) &&
        !has_same_handler_localized_continuation(handler, callsite)) {
      return false;
    }
    return callsite.unresolved_reason == "call_target_not_executable" ||
           callsite.unresolved_reason == "call_target_undecodable" ||
           callsite.unresolved_reason == "call_target_mid_instruction";
  };

  auto classify_frontier_reason =
      [&](const VirtualHandlerSummary &handler,
          const VirtualDispatchSummary &dispatch) {
        if (!dispatch.unresolved_reason.empty() &&
            dispatch.unresolved_reason != "dynamic_target") {
          return dispatch.unresolved_reason;
        }
        if (handler.stack_memory_budget_exceeded)
          return std::string("stack_fact_budget_exceeded");
        if (handler.has_unsupported_stack_memory)
          return std::string("unsupported_memory_target");
        for (const auto &callee_name : handler.direct_callees) {
          auto it = handler_by_name.find(callee_name);
          if (it == handler_by_name.end())
            continue;
          if (it->second->has_unsupported_stack_memory)
            return std::string("unsupported_memory_target");
          if (it->second->stack_memory_budget_exceeded)
            return std::string("stack_fact_budget_exceeded");
        }
        return std::string("dynamic_target");
      };

  for (const auto &root_handler : handlers) {
    if (!root_handler.is_output_root || !root_handler.entry_va.has_value())
      continue;

    VirtualRootSliceSummary slice;
    slice.root_va = *root_handler.entry_va;
    std::set<std::string> reachable_names;
    std::vector<const VirtualHandlerSummary *> worklist;
    enqueue_handler(&root_handler, worklist, reachable_names);

    while (!worklist.empty()) {
      const auto *handler = worklist.back();
      worklist.pop_back();

      for (const auto &callee_name : handler->direct_callees) {
        auto it = handler_by_name.find(callee_name);
        if (it != handler_by_name.end())
          enqueue_handler(it->second, worklist, reachable_names);
      }

      if (handler->entry_va.has_value()) {
        auto prelude =
            detectEntryPreludeDirectCall(binary_memory, *handler->entry_va);
        if (prelude.has_value()) {
          const VirtualHandlerSummary *target = nullptr;
          auto it = handler_by_pc.find(prelude->target_pc);
          if (it != handler_by_pc.end())
            target = it->second;
          if (target) {
            enqueue_handler(target, worklist, reachable_names);
          } else {
            auto reason = std::string("call_target_not_executable");
            std::optional<uint64_t> recovered_entry_pc;
            const VirtualHandlerSummary *recovered_target = nullptr;
            if (isTargetExecutable(binary_memory, prelude->target_pc)) {
              auto decodable = isTargetDecodableEntry(
                  binary_memory, prelude->target_pc, target_arch);
              if (decodable.has_value() && !*decodable) {
                recovered_target = findNearbyLiftedHandlerEntry(
                    handler_by_pc, prelude->target_pc, target_arch);
                if (recovered_target && recovered_target->entry_va.has_value()) {
                  recovered_entry_pc = recovered_target->entry_va;
                  enqueue_handler(recovered_target, worklist, reachable_names);
                  reason = std::string("call_target_mid_instruction");
                } else {
                  recovered_entry_pc = findNearbyExecutableEntry(
                      binary_memory, prelude->target_pc, target_arch);
                  if (recovered_entry_pc) {
                    auto recovered_it = handler_by_pc.find(*recovered_entry_pc);
                    if (recovered_it != handler_by_pc.end()) {
                      recovered_target = recovered_it->second;
                      enqueue_handler(recovered_target, worklist,
                                      reachable_names);
                      reason = std::string("call_target_mid_instruction");
                    } else {
                      reason = std::string("call_target_nearby_unlifted");
                    }
                  } else {
                    reason = std::string("call_target_undecodable");
                  }
                }
              } else {
                reason = std::string("call_target_unlifted");
              }
            } else if (isTargetMapped(binary_memory, prelude->target_pc)) {
              reason = std::string("call_target_not_executable");
            }
            slice.frontier_edges.push_back(VirtualRootSliceSummary::FrontierEdge{
                VirtualRootFrontierKind::kCall,
                handler->function_name,
                0,
                0,
                std::move(reason),
                prelude->target_pc,
                recovered_entry_pc,
                std::nullopt});
          }
        }
      }

      for (size_t dispatch_index = 0; dispatch_index < handler->dispatches.size();
           ++dispatch_index) {
        const auto &dispatch = handler->dispatches[dispatch_index];
        if (dispatch.successors.empty()) {
          slice.frontier_edges.push_back(
              VirtualRootSliceSummary::FrontierEdge{
                  VirtualRootFrontierKind::kDispatch,
                  handler->function_name, static_cast<unsigned>(dispatch_index),
                  0, classify_frontier_reason(*handler, dispatch),
                  std::nullopt, std::nullopt, std::nullopt});
          continue;
        }

        for (const auto &successor : dispatch.successors) {
          switch (successor.kind) {
            case VirtualSuccessorKind::kLiftedHandler:
            case VirtualSuccessorKind::kLiftedBlock:
            case VirtualSuccessorKind::kTraceBlock: {
              const VirtualHandlerSummary *target = nullptr;
              if (successor.target_function_name.has_value()) {
                auto it = handler_by_name.find(*successor.target_function_name);
                if (it != handler_by_name.end())
                  target = it->second;
              }
              if (!target && successor.target_pc != 0) {
                auto it = handler_by_pc.find(successor.target_pc);
                if (it != handler_by_pc.end())
                  target = it->second;
              }
              if (target) {
                enqueue_handler(target, worklist, reachable_names);
              } else {
                slice.frontier_edges.push_back(
                    VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0, "missing_lifted_target", successor.target_pc,
                        std::nullopt, std::nullopt});
              }
              break;
            }
            case VirtualSuccessorKind::kProtectedBoundary: {
              const VirtualHandlerSummary *target = nullptr;
              if (successor.canonical_boundary_target_va.has_value()) {
                auto it =
                    handler_by_pc.find(*successor.canonical_boundary_target_va);
                if (it != handler_by_pc.end())
                  target = it->second;
              }
              if (target) {
                enqueue_handler(target, worklist, reachable_names);
              } else {
                slice.frontier_edges.push_back(
                    VirtualRootSliceSummary::FrontierEdge{
                        VirtualRootFrontierKind::kDispatch,
                        handler->function_name,
                        static_cast<unsigned>(dispatch_index),
                        0, "boundary_target_unlifted", successor.target_pc,
                        successor.canonical_boundary_target_va,
                        successor.boundary_name});
              }
              break;
            }
            case VirtualSuccessorKind::kUnknown:
              slice.frontier_edges.push_back(
                  VirtualRootSliceSummary::FrontierEdge{
                      VirtualRootFrontierKind::kDispatch,
                      handler->function_name, static_cast<unsigned>(dispatch_index),
                      0,
                      dispatch.unresolved_reason.empty()
                          ? "missing_lifted_target"
                          : dispatch.unresolved_reason,
                      successor.target_pc, std::nullopt, std::nullopt});
              break;
          }
        }
      }

      for (size_t callsite_index = 0; callsite_index < handler->callsites.size();
           ++callsite_index) {
        const auto &callsite = handler->callsites[callsite_index];
        const VirtualHandlerSummary *target = nullptr;
        if (callsite.target_function_name.has_value()) {
          auto it = handler_by_name.find(*callsite.target_function_name);
          if (it != handler_by_name.end())
            target = it->second;
        }
        if (!target && callsite.resolved_target_pc.has_value()) {
          auto it = handler_by_pc.find(*callsite.resolved_target_pc);
          if (it != handler_by_pc.end())
            target = it->second;
        }
        if (!target && callsite.recovered_target_function_name.has_value()) {
          auto it = handler_by_name.find(*callsite.recovered_target_function_name);
          if (it != handler_by_name.end())
            target = it->second;
        }
        if (!target && callsite.recovered_entry_pc.has_value()) {
          auto it = handler_by_pc.find(*callsite.recovered_entry_pc);
          if (it != handler_by_pc.end())
            target = it->second;
        }
        if (target)
          enqueue_handler(target, worklist, reachable_names);

        if (is_semantically_localized_callsite(*handler, callsite))
          continue;

        if (!callsite.unresolved_reason.empty() || !target) {
          slice.frontier_edges.push_back(VirtualRootSliceSummary::FrontierEdge{
              VirtualRootFrontierKind::kCall,
              handler->function_name,
              0,
              static_cast<unsigned>(callsite_index),
              callsite.unresolved_reason.empty() ? "call_target_unlifted"
                                                 : callsite.unresolved_reason,
              callsite.resolved_target_pc, callsite.recovered_entry_pc,
              std::nullopt});
        }
      }

      for (const auto &boundary_name : handler->called_boundaries) {
        const auto *boundary = model.lookupBoundary(boundary_name);
        if (!boundary || !boundary->target_va.has_value())
          continue;
        auto it = handler_by_pc.find(*boundary->target_va);
        if (it != handler_by_pc.end()) {
          enqueue_handler(it->second, worklist, reachable_names);
          continue;
        }
        slice.frontier_edges.push_back(VirtualRootSliceSummary::FrontierEdge{
            VirtualRootFrontierKind::kDispatch,
            handler->function_name, static_cast<unsigned>(handler->dispatches.size()),
            0,
            "boundary_target_unlifted", std::nullopt, boundary->target_va,
            normalizeBoundaryName(boundary->name)});
      }
    }

    slice.reachable_handler_names.assign(reachable_names.begin(),
                                         reachable_names.end());
    slice.specialization_count = static_cast<unsigned>(std::count_if(
        slice.reachable_handler_names.begin(), slice.reachable_handler_names.end(),
        [&](const std::string &handler_name) {
          auto it = handler_by_name.find(handler_name);
          if (it == handler_by_name.end())
            return false;
          const auto *handler = it->second;
          if (!handler->is_specialized)
            return false;
          return !handler->specialization_root_va.has_value() ||
                 *handler->specialization_root_va == slice.root_va;
        }));
    slice.is_closed = slice.frontier_edges.empty();
    root_slices.push_back(std::move(slice));
  }
}

static void summarizeVirtualRegions(VirtualMachineModel &model,
                                    const BinaryMemoryMap &binary_memory) {
  auto &regions = model.mutableRegions();
  regions.clear();

  const auto &handlers = model.handlers();
  if (handlers.empty())
    return;

  std::map<std::string, size_t> handler_index;
  for (size_t i = 0; i < handlers.size(); ++i)
    handler_index.emplace(handlers[i].function_name, i);

  std::vector<std::vector<size_t>> undirected_edges(handlers.size());
  std::vector<bool> boundary_seed(handlers.size(), false);
  std::vector<std::vector<std::string>> adjacent_boundary_names(handlers.size());
  auto is_region_eligible = [&](const VirtualHandlerSummary &summary) {
    if (summary.is_candidate)
      return true;
    auto name = llvm::StringRef(summary.function_name);
    return name.starts_with("sub_") || name.starts_with("blk_");
  };

  for (size_t i = 0; i < handlers.size(); ++i) {
    const auto &summary = handlers[i];
    auto &boundary_names = adjacent_boundary_names[i];
    for (const auto &boundary_name : summary.called_boundaries)
      boundary_names.push_back(normalizeBoundaryName(boundary_name));
    for (const auto &dispatch : summary.dispatches) {
      auto target_pc = evaluateVirtualExpr(dispatch.target, summary.outgoing_facts,
                                           summary.outgoing_stack_facts);
      if (!target_pc)
        target_pc = evaluateVirtualExpr(dispatch.target, summary.incoming_facts,
                                        summary.incoming_stack_facts);
      if (!target_pc)
        continue;
      auto boundary_name =
          resolveBoundaryNameForTarget(model, binary_memory, *target_pc);
      if (!boundary_name || llvm::is_contained(boundary_names, *boundary_name))
        continue;
      boundary_names.push_back(*boundary_name);
    }
    boundary_seed[i] = !boundary_names.empty();
    for (const auto &callee_name : summary.direct_callees) {
      auto it = handler_index.find(callee_name);
      if (it == handler_index.end())
        continue;
      undirected_edges[i].push_back(it->second);
      undirected_edges[it->second].push_back(i);
    }
  }

  auto merge_fact_maps = [](std::map<unsigned, VirtualValueExpr> &dst,
                            const std::vector<VirtualSlotFact> &facts) {
    for (const auto &fact : facts) {
      auto it = dst.find(fact.slot_id);
      if (it == dst.end()) {
        dst.emplace(fact.slot_id, fact.value);
        continue;
      }
      auto merged = mergeIncomingExpr(it->second, fact.value);
      if (merged.has_value()) {
        it->second = std::move(*merged);
      } else {
        it->second = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                      : fact.value.bit_width);
      }
    }
  };

  auto merge_stack_fact_maps = [](std::map<unsigned, VirtualValueExpr> &dst,
                                  const std::vector<VirtualStackFact> &facts) {
    for (const auto &fact : facts) {
      auto it = dst.find(fact.cell_id);
      if (it == dst.end()) {
        dst.emplace(fact.cell_id, fact.value);
        continue;
      }
      auto merged = mergeIncomingExpr(it->second, fact.value);
      if (merged.has_value()) {
        it->second = std::move(*merged);
      } else {
        it->second = unknownExpr(it->second.bit_width ? it->second.bit_width
                                                      : fact.value.bit_width);
      }
    }
  };

  std::vector<bool> visited(handlers.size(), false);
  unsigned next_region_id = 0;
  for (size_t seed = 0; seed < handlers.size(); ++seed) {
    if (visited[seed] || !boundary_seed[seed] ||
        !is_region_eligible(handlers[seed]))
      continue;

    std::vector<size_t> component;
    std::vector<size_t> worklist{seed};
    visited[seed] = true;
    while (!worklist.empty()) {
      size_t current = worklist.back();
      worklist.pop_back();
      component.push_back(current);
      for (size_t neighbor : undirected_edges[current]) {
        if (visited[neighbor] || !is_region_eligible(handlers[neighbor]))
          continue;
        visited[neighbor] = true;
        worklist.push_back(neighbor);
      }
    }

    std::set<size_t> component_set(component.begin(), component.end());
    std::set<std::string> boundary_names;
    std::set<std::string> handler_names;
    std::set<std::string> entry_handlers;
    std::set<std::string> exit_handlers;
    std::set<unsigned> live_in_ids;
    std::set<unsigned> written_ids;
    std::set<unsigned> live_in_stack_ids;
    std::set<unsigned> written_stack_ids;
    std::map<unsigned, VirtualValueExpr> incoming_map;
    std::map<unsigned, VirtualValueExpr> outgoing_map;
    std::map<unsigned, VirtualValueExpr> incoming_stack_map;
    std::map<unsigned, VirtualValueExpr> outgoing_stack_map;
    std::vector<VirtualRegionSummary::Edge> internal_edges;

    for (size_t index : component) {
      const auto &summary = handlers[index];
      handler_names.insert(summary.function_name);
      boundary_names.insert(adjacent_boundary_names[index].begin(),
                            adjacent_boundary_names[index].end());
      live_in_ids.insert(summary.live_in_slot_ids.begin(),
                         summary.live_in_slot_ids.end());
      written_ids.insert(summary.written_slot_ids.begin(),
                         summary.written_slot_ids.end());
      live_in_stack_ids.insert(summary.live_in_stack_cell_ids.begin(),
                               summary.live_in_stack_cell_ids.end());
      written_stack_ids.insert(summary.written_stack_cell_ids.begin(),
                               summary.written_stack_cell_ids.end());
      merge_fact_maps(incoming_map, summary.incoming_facts);
      merge_fact_maps(outgoing_map, summary.outgoing_facts);
      merge_stack_fact_maps(incoming_stack_map, summary.incoming_stack_facts);
      merge_stack_fact_maps(outgoing_stack_map, summary.outgoing_stack_facts);

      bool exits_region = !adjacent_boundary_names[index].empty();
      for (const auto &callee_name : summary.direct_callees) {
        auto callee_it = handler_index.find(callee_name);
        if (callee_it == handler_index.end() ||
            !component_set.count(callee_it->second)) {
          exits_region = true;
          continue;
        }
        internal_edges.push_back(
            VirtualRegionSummary::Edge{summary.function_name, callee_name});
      }
      if (exits_region)
        exit_handlers.insert(summary.function_name);

      bool has_region_predecessor = false;
      for (size_t pred : component) {
        if (pred == index)
          continue;
        if (std::find(handlers[pred].direct_callees.begin(),
                      handlers[pred].direct_callees.end(),
                      summary.function_name) !=
            handlers[pred].direct_callees.end()) {
          has_region_predecessor = true;
          break;
        }
      }
      if (!has_region_predecessor || !adjacent_boundary_names[index].empty())
        entry_handlers.insert(summary.function_name);
    }

    VirtualRegionSummary region;
    region.id = next_region_id++;
    region.boundary_names.assign(boundary_names.begin(), boundary_names.end());
    region.handler_names.assign(handler_names.begin(), handler_names.end());
    region.entry_handler_names.assign(entry_handlers.begin(),
                                      entry_handlers.end());
    region.exit_handler_names.assign(exit_handlers.begin(), exit_handlers.end());
    std::sort(internal_edges.begin(), internal_edges.end(),
              [](const VirtualRegionSummary::Edge &lhs,
                 const VirtualRegionSummary::Edge &rhs) {
                if (lhs.source_handler_name != rhs.source_handler_name)
                  return lhs.source_handler_name < rhs.source_handler_name;
                return lhs.target_handler_name < rhs.target_handler_name;
              });
    internal_edges.erase(
        std::unique(internal_edges.begin(), internal_edges.end(),
                    [](const VirtualRegionSummary::Edge &lhs,
                       const VirtualRegionSummary::Edge &rhs) {
                      return lhs.source_handler_name == rhs.source_handler_name &&
                             lhs.target_handler_name == rhs.target_handler_name;
                    }),
        internal_edges.end());
    region.internal_edges = std::move(internal_edges);
    region.live_in_slot_ids.assign(live_in_ids.begin(), live_in_ids.end());
    region.written_slot_ids.assign(written_ids.begin(), written_ids.end());
    region.live_in_stack_cell_ids.assign(live_in_stack_ids.begin(),
                                         live_in_stack_ids.end());
    region.written_stack_cell_ids.assign(written_stack_ids.begin(),
                                         written_stack_ids.end());
    for (const auto &[slot_id, value] : incoming_map)
      region.incoming_facts.push_back(VirtualSlotFact{slot_id, value});
    for (const auto &[slot_id, value] : outgoing_map)
      region.outgoing_facts.push_back(VirtualSlotFact{slot_id, value});
    for (const auto &[cell_id, value] : incoming_stack_map)
      region.incoming_stack_facts.push_back(VirtualStackFact{cell_id, value});
    for (const auto &[cell_id, value] : outgoing_stack_map)
      region.outgoing_stack_facts.push_back(VirtualStackFact{cell_id, value});
    regions.push_back(std::move(region));
  }
}

}  // namespace

llvm::AnalysisKey VirtualMachineModelAnalysis::Key;

std::string renderVirtualValueExpr(const VirtualValueExpr &expr) {
  auto render_offset = [](int64_t offset) {
    std::ostringstream os;
    if (offset < 0)
      os << "-0x" << std::hex << static_cast<uint64_t>(-offset);
    else
      os << "+0x" << std::hex << static_cast<uint64_t>(offset);
    return os.str();
  };

  switch (expr.kind) {
    case VirtualExprKind::kConstant: {
      if (!expr.constant.has_value())
        return "const(?)";
      std::ostringstream os;
      os << "0x" << std::hex << *expr.constant;
      return os.str();
    }
    case VirtualExprKind::kArgument:
      if (!expr.argument_index.has_value())
        return "arg(?)";
      return "arg" + std::to_string(*expr.argument_index);
    case VirtualExprKind::kStateSlot: {
      std::string base = expr.state_base_name.value_or("state");
      int64_t offset = expr.state_offset.value_or(0);
      return "slot(" + base + render_offset(offset) + ")";
    }
    case VirtualExprKind::kStackCell: {
      std::string base = expr.state_base_name.value_or("state");
      int64_t base_offset = expr.state_offset.value_or(0);
      int64_t cell_offset = expr.stack_offset.value_or(0);
      return "stack(slot(" + base + render_offset(base_offset) + ")" +
             render_offset(cell_offset) + ")";
    }
    case VirtualExprKind::kAdd:
    case VirtualExprKind::kSub:
    case VirtualExprKind::kMul:
    case VirtualExprKind::kXor:
    case VirtualExprKind::kAnd:
    case VirtualExprKind::kOr:
    case VirtualExprKind::kShl:
    case VirtualExprKind::kLShr:
    case VirtualExprKind::kAShr:
    case VirtualExprKind::kEq:
    case VirtualExprKind::kNe:
    case VirtualExprKind::kUlt:
    case VirtualExprKind::kUle:
    case VirtualExprKind::kUgt:
    case VirtualExprKind::kUge:
    case VirtualExprKind::kSlt:
    case VirtualExprKind::kSle:
    case VirtualExprKind::kSgt:
    case VirtualExprKind::kSge:
    case VirtualExprKind::kSelect:
    case VirtualExprKind::kPhi: {
      const char *op = "unknown";
      switch (expr.kind) {
        case VirtualExprKind::kAdd:
          op = "add";
          break;
        case VirtualExprKind::kSub:
          op = "sub";
          break;
        case VirtualExprKind::kMul:
          op = "mul";
          break;
        case VirtualExprKind::kXor:
          op = "xor";
          break;
        case VirtualExprKind::kAnd:
          op = "and";
          break;
        case VirtualExprKind::kOr:
          op = "or";
          break;
        case VirtualExprKind::kShl:
          op = "shl";
          break;
        case VirtualExprKind::kLShr:
          op = "lshr";
          break;
        case VirtualExprKind::kAShr:
          op = "ashr";
          break;
        case VirtualExprKind::kEq:
          op = "eq";
          break;
        case VirtualExprKind::kNe:
          op = "ne";
          break;
        case VirtualExprKind::kUlt:
          op = "ult";
          break;
        case VirtualExprKind::kUle:
          op = "ule";
          break;
        case VirtualExprKind::kUgt:
          op = "ugt";
          break;
        case VirtualExprKind::kUge:
          op = "uge";
          break;
        case VirtualExprKind::kSlt:
          op = "slt";
          break;
        case VirtualExprKind::kSle:
          op = "sle";
          break;
        case VirtualExprKind::kSgt:
          op = "sgt";
          break;
        case VirtualExprKind::kSge:
          op = "sge";
          break;
        case VirtualExprKind::kSelect:
          op = "select";
          break;
        case VirtualExprKind::kPhi:
          op = "phi";
          break;
        default:
          break;
      }
      std::ostringstream os;
      os << op << "(";
      for (size_t i = 0; i < expr.operands.size(); ++i) {
        if (i)
          os << ", ";
        os << renderVirtualValueExpr(expr.operands[i]);
      }
      os << ")";
      return os.str();
    }
    case VirtualExprKind::kUnknown:
      return "unknown";
  }

  return "unknown";
}

const VirtualBoundaryInfo *VirtualMachineModel::lookupBoundary(
    llvm::StringRef name) const {
  auto needle = normalizeBoundaryName(name);
  auto it = std::find_if(boundaries_.begin(), boundaries_.end(),
                         [&](const VirtualBoundaryInfo &info) {
                           return normalizeBoundaryName(info.name) == needle;
                         });
  return (it == boundaries_.end()) ? nullptr : &*it;
}

const VirtualHandlerSummary *VirtualMachineModel::lookupHandler(
    llvm::StringRef name) const {
  auto it = std::find_if(handlers_.begin(), handlers_.end(),
                         [&](const VirtualHandlerSummary &summary) {
                           return summary.function_name == name;
                         });
  return (it == handlers_.end()) ? nullptr : &*it;
}

const VirtualStateSlotInfo *VirtualMachineModel::lookupSlot(unsigned id) const {
  auto it = std::find_if(slots_.begin(), slots_.end(),
                         [&](const VirtualStateSlotInfo &info) {
                           return info.id == id;
                         });
  return (it == slots_.end()) ? nullptr : &*it;
}

const VirtualRegionSummary *VirtualMachineModel::lookupRegion(unsigned id) const {
  auto it = std::find_if(regions_.begin(), regions_.end(),
                         [&](const VirtualRegionSummary &summary) {
                           return summary.id == id;
                         });
  return (it == regions_.end()) ? nullptr : &*it;
}

const VirtualRegionSummary *VirtualMachineModel::lookupRegionForHandler(
    llvm::StringRef name) const {
  auto needle = name.str();
  auto it = std::find_if(regions_.begin(), regions_.end(),
                         [&](const VirtualRegionSummary &summary) {
                           return llvm::is_contained(summary.handler_names,
                                                     needle);
                         });
  return (it == regions_.end()) ? nullptr : &*it;
}

const VirtualRegionSummary *VirtualMachineModel::lookupRegionForBoundary(
    llvm::StringRef name) const {
  auto needle = normalizeBoundaryName(name);
  auto it = std::find_if(regions_.begin(), regions_.end(),
                         [&](const VirtualRegionSummary &summary) {
                           return std::any_of(
                               summary.boundary_names.begin(),
                               summary.boundary_names.end(),
                               [&](const std::string &boundary_name) {
                                 return normalizeBoundaryName(boundary_name) ==
                                        needle;
                               });
                         });
  return (it == regions_.end()) ? nullptr : &*it;
}

const VirtualRootSliceSummary *VirtualMachineModel::lookupRootSlice(
    uint64_t root_va) const {
  auto it = std::find_if(root_slices_.begin(), root_slices_.end(),
                         [&](const VirtualRootSliceSummary &summary) {
                           return summary.root_va == root_va;
                         });
  return (it == root_slices_.end()) ? nullptr : &*it;
}

std::vector<const VirtualHandlerSummary *>
VirtualMachineModel::candidateHandlers() const {
  std::vector<const VirtualHandlerSummary *> candidates;
  for (const auto &summary : handlers_) {
    if (summary.is_candidate)
      candidates.push_back(&summary);
  }
  return candidates;
}

VirtualMachineModelAnalysis::Result VirtualMachineModelAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  VirtualMachineModel model;
  const auto &binary_memory = MAM.getResult<BinaryMemoryAnalysis>(M);

  for (auto &F : M) {
    if (!isBoundaryFunction(F))
      continue;

    VirtualBoundaryInfo info;
    info.name = F.getName().str();
    info.kind = classifyBoundaryKind(F);
    uint64_t entry_va = extractEntryVA(F.getName());
    if (entry_va != 0)
      info.entry_va = entry_va;
    if (auto attr_entry = extractHexAttr(F, "omill.boundary_entry_va"))
      info.entry_va = attr_entry;
    info.target_va = extractHexAttr(F, "omill.boundary_target_va");
    model.boundaries_.push_back(std::move(info));
  }

  std::map<std::string, llvm::SmallVector<std::string, 8>> direct_callees;
  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    auto &callees = direct_callees[F.getName().str()];
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *call = llvm::dyn_cast<llvm::CallBase>(&I);
        if (!call)
          continue;
        auto *callee = call->getCalledFunction();
        if (!callee || callee->isDeclaration() ||
            callee->hasFnAttribute("omill.localized_continuation_shim")) {
          continue;
        }
        if (!llvm::is_contained(callees, callee->getName().str()))
          callees.push_back(callee->getName().str());
      }
    }
  }

  std::set<std::string> interesting_handlers;
  std::vector<std::string> worklist;
  for (auto &F : M) {
    if (!isLiftedOrHelperSeedFunction(F))
      continue;
    auto inserted = interesting_handlers.insert(F.getName().str()).second;
    if (inserted)
      worklist.push_back(F.getName().str());
  }

  while (!worklist.empty()) {
    auto current = worklist.back();
    worklist.pop_back();
    auto it = direct_callees.find(current);
    if (it == direct_callees.end())
      continue;
    for (const auto &callee_name : it->second) {
      if (interesting_handlers.insert(callee_name).second)
        worklist.push_back(callee_name);
    }
  }

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (F.hasFnAttribute("omill.localized_continuation_shim"))
      continue;
    if (!interesting_handlers.empty() &&
        !interesting_handlers.count(F.getName().str())) {
      continue;
    }
    model.handlers_.push_back(summarizeFunction(F));
  }

  canonicalizeVirtualState(model);
  propagateVirtualStateFacts(M, model, binary_memory);
  summarizeVirtualRegions(model, binary_memory);
  summarizeDispatchSuccessors(M, model, binary_memory);
  summarizeCallSites(M, model, binary_memory);
  summarizeRootSlices(M, model, binary_memory);

  return model;
}

}  // namespace omill
