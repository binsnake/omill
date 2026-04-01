#include "omill/Analysis/VirtualModel/Types.h"

#include <sstream>

namespace omill {

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
    case VirtualExprKind::kMemoryRead:
      if (expr.operands.size() != 1)
        return "mem(?)";
      return "mem(" + renderVirtualValueExpr(expr.operands.front()) + ")";
    case VirtualExprKind::kZExt:
    case VirtualExprKind::kSExt:
    case VirtualExprKind::kTrunc:
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
        case VirtualExprKind::kZExt:
          op = "zext";
          break;
        case VirtualExprKind::kSExt:
          op = "sext";
          break;
        case VirtualExprKind::kTrunc:
          op = "trunc";
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

std::string renderVirtualIncomingContextSourceKind(
    VirtualIncomingContextSourceKind kind) {
  switch (kind) {
    case VirtualIncomingContextSourceKind::kDirectCallsite:
      return "direct_callsite";
    case VirtualIncomingContextSourceKind::kEntryPrelude:
      return "entry_prelude";
    case VirtualIncomingContextSourceKind::kLocalizedCallee:
      return "localized_callee";
  }
  return "direct_callsite";
}

static std::string renderVirtualIncomingContextArm(
    const VirtualIncomingContextArm &arm, const char *label, unsigned id) {
  std::ostringstream os;
  os << label << "[" << id << "] from " << arm.edge_identity << " ("
     << renderVirtualIncomingContextSourceKind(arm.source_kind);
  if (!arm.source_handler_name.empty())
    os << ", handler=" << arm.source_handler_name;
  os << ", site=" << arm.source_site_index << ") = "
     << renderVirtualValueExpr(arm.value);
  return os.str();
}

std::string renderVirtualIncomingSlotPhi(const VirtualIncomingSlotPhi &phi) {
  std::ostringstream os;
  os << "slot[" << phi.slot_id << "] merged="
     << renderVirtualValueExpr(phi.merged_value);
  for (const auto &arm : phi.arms)
    os << " ; " << renderVirtualIncomingContextArm(arm, "slot", phi.slot_id);
  return os.str();
}

std::string renderVirtualIncomingStackPhi(const VirtualIncomingStackPhi &phi) {
  std::ostringstream os;
  os << "cell[" << phi.cell_id << "] merged="
     << renderVirtualValueExpr(phi.merged_value);
  for (const auto &arm : phi.arms)
    os << " ; " << renderVirtualIncomingContextArm(arm, "cell", phi.cell_id);
  return os.str();
}

}  // namespace omill
