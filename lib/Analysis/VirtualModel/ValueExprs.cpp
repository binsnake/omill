#include "Analysis/VirtualModel/Internal.h"

#include <llvm/ADT/SmallPtrSet.h>
#include <llvm/Analysis/ValueTracking.h>
#include <llvm/IR/Argument.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Type.h>

#include <algorithm>
#include <cstring>
#include <functional>

#include "omill/Utils/StateFieldMap.h"

namespace omill::virtual_model::detail {

namespace {

}  // namespace

std::optional<unsigned> remillMemoryBitWidth(llvm::StringRef name) {
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

namespace {

static llvm::Module *moduleForValue(llvm::Value *V) {
  if (auto *I = llvm::dyn_cast<llvm::Instruction>(V))
    return I->getModule();
  if (auto *A = llvm::dyn_cast<llvm::Argument>(V))
    return A->getParent() ? A->getParent()->getParent() : nullptr;
  if (auto *F = llvm::dyn_cast<llvm::Function>(V))
    return F->getParent();
  return nullptr;
}

static VirtualValueExpr summarizeValueExprImpl(
    llvm::Value *V, const llvm::DataLayout &dl,
    llvm::SmallPtrSetImpl<llvm::Value *> &visited, unsigned depth) {
  VirtualValueExpr expr;
  expr.bit_width = getValueBitWidth(V, dl);
  const auto native_sp_offset = nativeStackPointerOffsetForValue(V);

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
                                                      width.getFixedValue(),
                                                      native_sp_offset)) {
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
        return castExpr(inner, cast->getOpcode(),
                        expr.bit_width ? expr.bit_width : inner.bit_width);
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
      expr.kind = VirtualExprKind::kMemoryRead;
      expr.complete = pointer_expr.complete;
      expr.operands.push_back(std::move(pointer_expr));
      if (auto cell = extractStackCellSummaryFromExpr(
              expr.operands.front(), getValueBitWidth(V, dl) / 8,
              native_sp_offset)) {
        expr.kind = VirtualExprKind::kStackCell;
        expr.state_base_name = cell->base_name;
        expr.state_offset = cell->base_offset;
        expr.stack_offset = cell->offset;
        expr.bit_width = cell->width ? (cell->width * 8u) : expr.bit_width;
      }
      return expr;
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

}  // namespace

bool isRemillReadMemoryIntrinsic(const llvm::Function &F) {
  return remillMemoryBitWidth(F.getName()).has_value() &&
         F.getName().starts_with("__remill_read_memory_");
}

bool isRemillWriteMemoryIntrinsic(const llvm::Function &F) {
  return remillMemoryBitWidth(F.getName()).has_value() &&
         F.getName().starts_with("__remill_write_memory_");
}

bool isRemillTerminalControlIntrinsic(const llvm::Function &F) {
  return F.getName() == "__remill_missing_block" ||
         F.getName() == "__remill_function_return";
}

unsigned getValueBitWidth(llvm::Value *V, const llvm::DataLayout &dl) {
  auto *ty = V->getType();
  if (ty->isIntegerTy())
    return ty->getIntegerBitWidth();
  if (ty->isPointerTy())
    return dl.getPointerSizeInBits(ty->getPointerAddressSpace());
  return 0;
}

std::optional<VirtualStateSlotSummary> extractStateSlotSummary(
    llvm::Value *ptr, unsigned width, const llvm::DataLayout &dl) {
  int64_t offset = 0;
  auto *base = llvm::GetPointerBaseWithConstantOffset(ptr, offset, dl, true);
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

std::optional<unsigned> nativeStackPointerOffsetForValue(llvm::Value *V) {
  auto *M = moduleForValue(V);
  if (!M)
    return std::nullopt;
  StateFieldMap field_map(*M);
  for (const char *sp_name : {"RSP", "SP", "sp"}) {
    if (auto field = field_map.fieldByName(sp_name))
      return field->offset;
  }
  return std::nullopt;
}

std::optional<VirtualStackCellSummary> extractStackCellSummaryFromExpr(
    const VirtualValueExpr &expr, unsigned width,
    std::optional<unsigned> native_sp_offset) {
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
  auto get_base_summary = [&](const VirtualValueExpr &value)
      -> std::optional<BaseSummary> {
    if (value.kind == VirtualExprKind::kStateSlot &&
        value.state_base_name.has_value() && value.state_offset.has_value()) {
      auto base_name = *value.state_base_name;
      const bool from_argument = llvm::StringRef(base_name).starts_with("arg");
      bool is_stack_base = false;
      if (from_argument) {
        is_stack_base = !native_sp_offset.has_value() ||
                        *value.state_offset ==
                            static_cast<int64_t>(*native_sp_offset);
      } else {
        llvm::StringRef name(base_name);
        is_stack_base = name.equals_insensitive("RSP") ||
                        name.equals_insensitive("SP");
      }
      if (!is_stack_base)
        return std::nullopt;
      return BaseSummary{base_name, *value.state_offset, expr_width_bytes(value),
                         from_argument, !from_argument};
    }

    if (!native_sp_offset.has_value() && value.kind == VirtualExprKind::kArgument &&
        value.argument_index.has_value()) {
      return BaseSummary{"arg" + std::to_string(*value.argument_index), 0,
                         expr_width_bytes(value), true, false};
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

std::optional<unsigned> lookupNativeStackPointerOffset(llvm::Module &M) {
  StateFieldMap field_map(M);
  for (const char *sp_name : {"RSP", "SP", "sp"}) {
    if (auto field = field_map.fieldByName(sp_name))
      return field->offset;
  }
  return std::nullopt;
}

uint64_t bitMask(unsigned bits) {
  if (bits == 0 || bits >= 64)
    return ~0ULL;
  return (1ULL << bits) - 1;
}

uint64_t signExtendBits(uint64_t value, unsigned from_bits) {
  if (from_bits == 0 || from_bits >= 64)
    return value;
  uint64_t masked = value & bitMask(from_bits);
  uint64_t sign_bit = 1ULL << (from_bits - 1);
  if ((masked & sign_bit) == 0)
    return masked;
  return masked | ~bitMask(from_bits);
}

VirtualValueExpr constantExpr(uint64_t value, unsigned bits) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kConstant;
  expr.bit_width = bits;
  expr.complete = true;
  expr.constant = value & bitMask(bits);
  return expr;
}

VirtualValueExpr argumentExpr(unsigned index, unsigned bits) {
  VirtualValueExpr expr;
  expr.kind = VirtualExprKind::kArgument;
  expr.bit_width = bits;
  expr.complete = true;
  expr.argument_index = index;
  return expr;
}

VirtualValueExpr castExpr(const VirtualValueExpr &expr,
                          llvm::Instruction::CastOps opcode,
                          unsigned target_bits) {
  VirtualValueExpr casted = expr;
  unsigned source_bits = expr.bit_width ? expr.bit_width : target_bits;
  if (source_bits == target_bits &&
      (opcode == llvm::Instruction::BitCast ||
       opcode == llvm::Instruction::PtrToInt ||
       opcode == llvm::Instruction::IntToPtr)) {
    casted.bit_width = target_bits;
    return casted;
  }
  casted.bit_width = target_bits;
  if (!casted.constant.has_value() && casted.kind == VirtualExprKind::kPhi) {
    casted.operands.clear();
    casted.complete = true;
    for (const auto &operand : expr.operands) {
      casted.operands.push_back(castExpr(operand, opcode, target_bits));
      casted.complete &= casted.operands.back().complete;
    }
    return casted;
  }
  if (!casted.constant.has_value() && casted.kind == VirtualExprKind::kSelect &&
      casted.operands.size() == 3) {
    casted.operands.clear();
    casted.operands.push_back(expr.operands[0]);
    casted.operands.push_back(castExpr(expr.operands[1], opcode, target_bits));
    casted.operands.push_back(castExpr(expr.operands[2], opcode, target_bits));
    casted.complete = std::all_of(
        casted.operands.begin(), casted.operands.end(),
        [](const VirtualValueExpr &operand) { return operand.complete; });
    return casted;
  }
  if (!casted.constant.has_value()) {
    switch (opcode) {
      case llvm::Instruction::ZExt:
      case llvm::Instruction::PtrToInt:
      case llvm::Instruction::IntToPtr:
        casted.kind = VirtualExprKind::kZExt;
        casted.operands = {expr};
        casted.complete = expr.complete;
        return casted;
      case llvm::Instruction::SExt:
        casted.kind = VirtualExprKind::kSExt;
        casted.operands = {expr};
        casted.complete = expr.complete;
        return casted;
      case llvm::Instruction::Trunc:
        casted.kind = VirtualExprKind::kTrunc;
        casted.operands = {expr};
        casted.complete = expr.complete;
        return casted;
      case llvm::Instruction::BitCast:
        return casted;
      default:
        return casted;
    }
  }

  if (!casted.constant.has_value())
    return casted;

  uint64_t value = *casted.constant;
  switch (opcode) {
    case llvm::Instruction::ZExt:
    case llvm::Instruction::BitCast:
    case llvm::Instruction::PtrToInt:
    case llvm::Instruction::IntToPtr:
      casted.constant = value & bitMask(std::min(source_bits, target_bits));
      break;
    case llvm::Instruction::SExt:
      casted.constant =
          signExtendBits(value, source_bits) & bitMask(target_bits);
      break;
    case llvm::Instruction::Trunc:
      casted.constant = value & bitMask(target_bits);
      break;
    default:
      break;
  }
  return casted;
}

VirtualExprKind classifyExprKind(unsigned opcode) {
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

VirtualExprKind classifyICmpPredicate(llvm::CmpInst::Predicate pred) {
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

VirtualValueExpr summarizeValueExpr(llvm::Value *V,
                                    const llvm::DataLayout &dl) {
  llvm::SmallPtrSet<llvm::Value *, 16> visited;
  return summarizeValueExprImpl(V, dl, visited, 0);
}

}  // namespace omill::virtual_model::detail
