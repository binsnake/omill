#include "omill/Passes/RecoverFunctionSignatures.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/StringRef.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/DataLayout.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <cctype>
#include <functional>
#include <memory>

#include "omill/Analysis/CallingConventionAnalysis.h"
#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

namespace {

bool debugPublicRootSeeds() {
  static bool enabled = std::getenv("OMILL_DEBUG_PUBLIC_ROOT_SEEDS") != nullptr;
  return enabled;
}

std::string nativeWrapperName(const llvm::Function &F) {
  return F.getName().str() + "_native";
}

bool isPublicOutputRoot(const llvm::Function *F) {
  return F && F->hasFnAttribute("omill.output_root") &&
         !F->hasFnAttribute("omill.vm_wrapper") &&
         !F->hasFnAttribute("omill.internal_output_root");
}

bool shouldRecoverClosedRootSliceFunction(const llvm::Function &F) {
  if (!isClosedRootSliceScopedModule(*F.getParent()))
    return true;
  return isClosedRootSliceFunction(F);
}

bool isTerminalMissingBlockStub(const llvm::Function &F) {
  const llvm::Function *missing_block = nullptr;
  unsigned direct_calls = 0;

  for (const auto &BB : F) {
    for (const auto &I : BB) {
      const auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;
      auto *callee = CB->getCalledFunction();
      if (!callee)
        return false;
      ++direct_calls;
      if (callee->getName() != "__remill_missing_block")
        return false;
      missing_block = callee;
    }
  }

  return missing_block != nullptr && direct_calls == 1;
}

unsigned exportedRootGPRParamCount(const FunctionABI &abi,
                                   bool is_public_output_root) {
  if (!is_public_output_root)
    return abi.numParams();
  return abi.numParams();
}

std::optional<unsigned> getStateByteOffset(const llvm::Function &F,
                                           const llvm::Value *ptr,
                                           const llvm::DataLayout &DL) {
  auto *state_arg = F.arg_empty() ? nullptr : F.getArg(0);
  if (!state_arg)
    return std::nullopt;

  auto *gep =
      llvm::dyn_cast<llvm::GEPOperator>(ptr->stripPointerCasts());
  if (!gep || gep->getPointerOperand() != state_arg)
    return std::nullopt;

  llvm::APInt offset(DL.getIndexTypeSizeInBits(gep->getPointerOperandType()),
                     0);
  if (!gep->accumulateConstantOffset(DL, offset))
    return std::nullopt;

  return static_cast<unsigned>(offset.getZExtValue());
}

struct EntrySeedValue {
  enum class Kind {
    Constant,
    ProgramCounterRelative,
  };

  Kind kind = Kind::Constant;
  int64_t value = 0;
};

struct DriverSeedExpr {
  enum class Kind {
    Param,
    Constant,
    Add64,
    Xor64,
    Xor32,
    And32,
    ZExt32,
    Rol64,
    Ror64,
  };

  Kind kind = Kind::Constant;
  uint64_t constant = 0;
  unsigned param_index = 0;
  std::unique_ptr<DriverSeedExpr> lhs;
  std::unique_ptr<DriverSeedExpr> rhs;
};

class DriverSeedExprParser {
 public:
  explicit DriverSeedExprParser(llvm::StringRef text) : text_(text) {}

  std::unique_ptr<DriverSeedExpr> parse() {
    auto expr = parseExpr();
    skipWS();
    if (!expr || pos_ != text_.size())
      return nullptr;
    return expr;
  }

 private:
  llvm::StringRef text_;
  size_t pos_ = 0;

  void skipWS() {
    while (pos_ < text_.size() &&
           std::isspace(static_cast<unsigned char>(text_[pos_])))
      ++pos_;
  }

  bool consume(char c) {
    skipWS();
    if (pos_ >= text_.size() || text_[pos_] != c)
      return false;
    ++pos_;
    return true;
  }

  std::optional<llvm::StringRef> parseIdentifier() {
    skipWS();
    size_t start = pos_;
    while (pos_ < text_.size() &&
           (std::isalnum(static_cast<unsigned char>(text_[pos_])) ||
            text_[pos_] == '_'))
      ++pos_;
    if (start == pos_)
      return std::nullopt;
    return text_.slice(start, pos_);
  }

  std::optional<uint64_t> parseUInt() {
    skipWS();
    size_t start = pos_;
    if (pos_ + 2 <= text_.size() && text_[pos_] == '0' &&
        (text_[pos_ + 1] == 'x' || text_[pos_ + 1] == 'X')) {
      pos_ += 2;
      size_t hex_start = pos_;
      while (pos_ < text_.size() &&
             std::isxdigit(static_cast<unsigned char>(text_[pos_])))
        ++pos_;
      if (hex_start == pos_)
        return std::nullopt;
      uint64_t value = 0;
      if (text_.slice(hex_start, pos_).getAsInteger(16, value))
        return std::nullopt;
      return value;
    }
    while (pos_ < text_.size() &&
           std::isdigit(static_cast<unsigned char>(text_[pos_])))
      ++pos_;
    if (start == pos_)
      return std::nullopt;
    uint64_t value = 0;
    if (text_.slice(start, pos_).getAsInteger(10, value))
      return std::nullopt;
    return value;
  }

  std::unique_ptr<DriverSeedExpr> parseUnaryCall(DriverSeedExpr::Kind kind) {
    if (!consume('('))
      return nullptr;
    auto inner = parseExpr();
    if (!inner || !consume(')'))
      return nullptr;
    auto expr = std::make_unique<DriverSeedExpr>();
    expr->kind = kind;
    expr->lhs = std::move(inner);
    return expr;
  }

  std::unique_ptr<DriverSeedExpr> parseBinaryCall(DriverSeedExpr::Kind kind) {
    if (!consume('('))
      return nullptr;
    auto lhs = parseExpr();
    if (!lhs || !consume(','))
      return nullptr;
    auto rhs = parseExpr();
    if (!rhs || !consume(')'))
      return nullptr;
    auto expr = std::make_unique<DriverSeedExpr>();
    expr->kind = kind;
    expr->lhs = std::move(lhs);
    expr->rhs = std::move(rhs);
    return expr;
  }

  std::unique_ptr<DriverSeedExpr> parseExpr() {
    auto ident = parseIdentifier();
    if (!ident)
      return nullptr;

    if (*ident == "param") {
      if (!consume('('))
        return nullptr;
      auto index = parseUInt();
      if (!index || !consume(')'))
        return nullptr;
      auto expr = std::make_unique<DriverSeedExpr>();
      expr->kind = DriverSeedExpr::Kind::Param;
      expr->param_index = static_cast<unsigned>(*index);
      return expr;
    }

    if (*ident == "const") {
      if (!consume('('))
        return nullptr;
      auto value = parseUInt();
      if (!value || !consume(')'))
        return nullptr;
      auto expr = std::make_unique<DriverSeedExpr>();
      expr->kind = DriverSeedExpr::Kind::Constant;
      expr->constant = *value;
      return expr;
    }

    if (*ident == "add64")
      return parseBinaryCall(DriverSeedExpr::Kind::Add64);
    if (*ident == "xor64")
      return parseBinaryCall(DriverSeedExpr::Kind::Xor64);
    if (*ident == "xor32")
      return parseBinaryCall(DriverSeedExpr::Kind::Xor32);
    if (*ident == "and32")
      return parseBinaryCall(DriverSeedExpr::Kind::And32);
    if (*ident == "rol64")
      return parseBinaryCall(DriverSeedExpr::Kind::Rol64);
    if (*ident == "ror64")
      return parseBinaryCall(DriverSeedExpr::Kind::Ror64);
    if (*ident == "zext32")
      return parseUnaryCall(DriverSeedExpr::Kind::ZExt32);

    return nullptr;
  }
};

using DriverSeedExprMap =
    llvm::SmallVector<std::pair<std::string, std::unique_ptr<DriverSeedExpr>>, 8>;

llvm::SmallVector<std::optional<unsigned>, 8>
collectParamStateOffsets(const llvm::Function &F) {
  llvm::SmallVector<std::optional<unsigned>, 8> result;
  auto attr = F.getFnAttribute("omill.param_state_offsets");
  if (!attr.isValid() || !attr.isStringAttribute())
    return result;

  llvm::SmallVector<llvm::StringRef, 8> entries;
  attr.getValueAsString().split(entries, ',', -1, false);
  for (auto entry : entries) {
    entry = entry.trim();
    if (entry.empty())
      continue;
    if (entry == "stack") {
      result.push_back(std::nullopt);
      continue;
    }
    unsigned offset = 0;
    if (entry.getAsInteger(10, offset))
      result.push_back(std::nullopt);
    else
      result.push_back(offset);
  }
  return result;
}

DriverSeedExprMap collectDriverProvidedPublicRootSeedExprs(
    const llvm::Function &F) {
  DriverSeedExprMap result;
  auto attr = F.getFnAttribute("omill.export_entry_seed_exprs");
  if (!attr.isValid() || !attr.isStringAttribute())
    return result;

  llvm::SmallVector<llvm::StringRef, 8> entries;
  attr.getValueAsString().split(entries, ';', -1, false);
  for (auto entry : entries) {
    entry = entry.trim();
    if (entry.empty())
      continue;
    auto parts = entry.split('=');
    if (parts.first.empty() || parts.second.empty())
      continue;
    DriverSeedExprParser parser(parts.second.trim());
    auto expr = parser.parse();
    if (!expr)
      continue;
    result.emplace_back(parts.first.trim().str(), std::move(expr));
  }

  return result;
}

llvm::Value *evaluateDriverSeedExpr(
    const DriverSeedExpr &expr, llvm::IRBuilder<> &Builder,
    const std::function<llvm::Value *(unsigned)> &get_param_value) {
  auto *i64_ty = Builder.getInt64Ty();
  auto i64 = [&](uint64_t value) { return llvm::ConstantInt::get(i64_ty, value); };
  auto mask32 = [&]() { return i64(0xffffffffull); };
  auto eval = [&](const DriverSeedExpr &node,
                  const auto &self) -> llvm::Value * {
    switch (node.kind) {
      case DriverSeedExpr::Kind::Param:
        return get_param_value(node.param_index);
      case DriverSeedExpr::Kind::Constant:
        return i64(node.constant);
      case DriverSeedExpr::Kind::Add64:
        return Builder.CreateAdd(self(*node.lhs, self), self(*node.rhs, self));
      case DriverSeedExpr::Kind::Xor64:
        return Builder.CreateXor(self(*node.lhs, self), self(*node.rhs, self));
      case DriverSeedExpr::Kind::Xor32: {
        auto *value =
            Builder.CreateXor(self(*node.lhs, self), self(*node.rhs, self));
        return Builder.CreateAnd(value, mask32());
      }
      case DriverSeedExpr::Kind::And32: {
        auto *value =
            Builder.CreateAnd(self(*node.lhs, self), self(*node.rhs, self));
        return Builder.CreateAnd(value, mask32());
      }
      case DriverSeedExpr::Kind::ZExt32:
        return Builder.CreateAnd(self(*node.lhs, self), mask32());
      case DriverSeedExpr::Kind::Rol64:
        return Builder.CreateIntrinsic(
            i64_ty, llvm::Intrinsic::fshl,
            {self(*node.lhs, self), self(*node.lhs, self),
             self(*node.rhs, self)});
      case DriverSeedExpr::Kind::Ror64:
        return Builder.CreateIntrinsic(
            i64_ty, llvm::Intrinsic::fshr,
            {self(*node.lhs, self), self(*node.lhs, self),
             self(*node.rhs, self)});
    }
    llvm_unreachable("unknown driver seed expr kind");
  };

  return eval(expr, eval);
}

std::optional<EntrySeedValue> analyzeEntrySeedValue(const llvm::Value *V,
                                                    const llvm::Function &F) {
  auto *program_counter_arg = F.arg_size() > 1 ? F.getArg(1) : nullptr;
  V = V->stripPointerCasts();

  if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(V)) {
    return EntrySeedValue{
        EntrySeedValue::Kind::Constant,
        static_cast<int64_t>(CI->getValue().zextOrTrunc(64).getZExtValue()),
    };
  }

  if (program_counter_arg && V == program_counter_arg) {
    return EntrySeedValue{
        EntrySeedValue::Kind::ProgramCounterRelative,
        0,
    };
  }

  auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(V);
  if (!BO || !program_counter_arg)
    return std::nullopt;

  auto eval_pc_relative = [&](llvm::Value *lhs, llvm::Value *rhs,
                              bool rhs_is_subtrahend)
      -> std::optional<EntrySeedValue> {
    if (lhs != program_counter_arg)
      return std::nullopt;
    auto *CI = llvm::dyn_cast<llvm::ConstantInt>(rhs);
    if (!CI)
      return std::nullopt;
    int64_t delta = CI->getSExtValue();
    if (rhs_is_subtrahend)
      delta = -delta;
    return EntrySeedValue{
        EntrySeedValue::Kind::ProgramCounterRelative,
        delta,
    };
  };

  switch (BO->getOpcode()) {
    case llvm::Instruction::Add:
      if (auto seed =
              eval_pc_relative(BO->getOperand(0), BO->getOperand(1), false)) {
        return seed;
      }
      return eval_pc_relative(BO->getOperand(1), BO->getOperand(0), false);
    case llvm::Instruction::Sub:
      return eval_pc_relative(BO->getOperand(0), BO->getOperand(1), true);
    default:
      return std::nullopt;
  }
}

std::optional<EntrySeedValue> findEntrySeedValueForStateOffset(
    const llvm::Function &F,
    unsigned state_offset,
    const llvm::DataLayout &DL) {
  if (F.empty())
    return std::nullopt;

  for (const auto &I : F.getEntryBlock()) {
    if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
      auto load_offset = getStateByteOffset(F, LI->getPointerOperand(), DL);
      if (load_offset && *load_offset == state_offset)
        return std::nullopt;
      continue;
    }

    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto store_offset = getStateByteOffset(F, SI->getPointerOperand(), DL);
      if (!store_offset || *store_offset != state_offset)
        continue;
      return analyzeEntrySeedValue(SI->getValueOperand(), F);
    }

    if (llvm::isa<llvm::CallBase>(I))
      return std::nullopt;
  }

  return std::nullopt;
}

std::optional<uint64_t> findEntryConstantSeedForStateOffset(
    const llvm::Function &F,
    unsigned state_offset,
    const llvm::DataLayout &DL) {
  auto seed = findEntrySeedValueForStateOffset(F, state_offset, DL);
  if (!seed || seed->kind != EntrySeedValue::Kind::Constant)
    return std::nullopt;
  return static_cast<uint64_t>(seed->value);
}

std::optional<EntrySeedValue> findEntryLateSeedValueForStateOffset(
    const llvm::Function &F,
    unsigned state_offset,
    const llvm::DataLayout &DL) {
  if (F.empty())
    return std::nullopt;

  for (const auto &I : F.getEntryBlock()) {
    if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
      auto store_offset = getStateByteOffset(F, SI->getPointerOperand(), DL);
      if (!store_offset || *store_offset != state_offset)
        continue;
      return analyzeEntrySeedValue(SI->getValueOperand(), F);
    }

    if (llvm::isa<llvm::CallBase>(I))
      return std::nullopt;
  }

  return std::nullopt;
}

llvm::SmallVector<std::optional<uint64_t>, 2>
detectPublicRootForcedGPRPrefixConstants(const llvm::Function &F,
                                         const FunctionABI &abi,
                                         unsigned gpr_param_count) {
  llvm::SmallVector<std::optional<uint64_t>, 2> constants;
  const auto &DL = F.getParent()->getDataLayout();
  for (unsigned i = 0; i < gpr_param_count; ++i) {
    auto constant =
        findEntryConstantSeedForStateOffset(F, abi.params[i].state_offset, DL);
    if (!constant.has_value())
      break;
    constants.push_back(constant);
  }
  return constants;
}

llvm::DenseMap<unsigned, EntrySeedValue>
detectPublicRootExtraGPRSeeds(const llvm::Function &F, const FunctionABI &abi) {
  llvm::DenseMap<unsigned, EntrySeedValue> seeds;
  const auto &DL = F.getParent()->getDataLayout();
  for (unsigned off : abi.extra_gpr_live_ins) {
    auto seed = findEntryLateSeedValueForStateOffset(F, off, DL);
    if (!seed)
      continue;
    seeds.insert({off, *seed});
  }
  return seeds;
}

llvm::DenseMap<unsigned, EntrySeedValue>
detectPublicRootHiddenNonParamGPRSeeds(const llvm::Function &F,
                                       const FunctionABI &abi,
                                       const StateFieldMap &field_map) {
  llvm::DenseMap<unsigned, EntrySeedValue> seeds;
  const auto &DL = F.getParent()->getDataLayout();

  llvm::DenseSet<unsigned> excluded_offsets;
  for (const auto &param : abi.params)
    excluded_offsets.insert(param.state_offset);
  for (unsigned off : abi.extra_gpr_live_ins)
    excluded_offsets.insert(off);
  if (auto sp = field_map.fieldByName("RSP"); sp.has_value())
    excluded_offsets.insert(sp->offset);
  if (auto sp = field_map.fieldByName("SP"); sp.has_value())
    excluded_offsets.insert(sp->offset);
  if (auto sp = field_map.fieldByName("sp"); sp.has_value())
    excluded_offsets.insert(sp->offset);

  static constexpr const char *kCandidateRegs[] = {
      "RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "R8",
      "R9",  "R10", "R11", "R12", "R13", "R14", "R15",
  };

  for (const char *name : kCandidateRegs) {
    auto field = field_map.fieldByName(name);
    if (!field.has_value() || excluded_offsets.contains(field->offset))
      continue;
    auto seed = findEntryLateSeedValueForStateOffset(F, field->offset, DL);
    if (!seed)
      continue;
    seeds.insert({field->offset, *seed});
  }

  return seeds;
}

/// Build a native function type from recovered ABI info.
llvm::FunctionType *buildNativeType(const FunctionABI &abi,
                                     llvm::LLVMContext &Ctx,
                                     bool suppress_extra_gpr_returns = false,
                                     unsigned gpr_param_count = 0,
                                     bool suppress_non_standard_params = false,
                                     bool expose_public_root_ptr_params = false) {
  auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
  auto *xmm_ty = llvm::FixedVectorType::get(i64_ty, 2);
  auto *ptr_ty = llvm::PointerType::get(Ctx, 0);

  // --- Return type ---
  // If the function clobbers callee-saved GPRs, we pack the primary return
  // value (RAX/XMM0/void) together with the clobbered register values into a
  // struct return.  At call sites the caller extracts and stores each field
  // back into its own State so that interprocedural register flow is kept.
  llvm::Type *primary_ret_ty;
  if (abi.ret.has_value()) {
    primary_ret_ty =
        abi.ret->is_vector ? static_cast<llvm::Type *>(xmm_ty) : i64_ty;
  } else {
    primary_ret_ty = nullptr;  // void
  }

  llvm::Type *ret_ty;
  bool use_struct_return =
      abi.hasStructReturn() && !suppress_extra_gpr_returns;
  if (use_struct_return) {
    llvm::SmallVector<llvm::Type *, 10> fields;
    if (primary_ret_ty)
      fields.push_back(primary_ret_ty);
    for (unsigned i = 0; i < abi.numExtraGPRReturns(); ++i)
      fields.push_back(i64_ty);
    ret_ty = llvm::StructType::get(Ctx, fields);
  } else if (primary_ret_ty) {
    ret_ty = primary_ret_ty;
  } else {
    ret_ty = llvm::Type::getVoidTy(Ctx);
  }

  // --- Parameters ---
  llvm::SmallVector<llvm::Type *, 10> param_types;

  // GPR params (i64).
  if (gpr_param_count == 0)
    gpr_param_count = abi.numParams();
  for (unsigned i = 0; i < gpr_param_count; ++i)
    param_types.push_back(
        expose_public_root_ptr_params
            ? static_cast<llvm::Type *>(ptr_ty)
            : static_cast<llvm::Type *>(i64_ty));

  if (suppress_non_standard_params)
    return llvm::FunctionType::get(ret_ty, param_types, false);

  // Stack-passed params (i64 each).
  for (unsigned i = 0; i < abi.numStackParams(); ++i)
    param_types.push_back(i64_ty);

  // XMM live-ins (<2 x i64>).
  for (unsigned i = 0; i < abi.numXMMParams(); ++i)
    param_types.push_back(xmm_ty);

  // Extra GPR live-ins (i64).
  for (unsigned i = 0; i < abi.numExtraGPRParams(); ++i)
    param_types.push_back(i64_ty);

  return llvm::FunctionType::get(ret_ty, param_types, false);
}

/// Build a GEP to a State field at a given byte offset using i8 arithmetic.
llvm::Value *buildStateGEP(llvm::IRBuilder<> &Builder, llvm::Value *state_ptr,
                            unsigned offset) {
  auto *gep = Builder.CreateConstGEP1_64(Builder.getInt8Ty(), state_ptr, offset);
  return gep;
}

/// Create a native wrapper function that:
/// 1. Allocates a local State struct
/// 2. Stores parameters into the appropriate State fields
/// 3. Calls the original lifted function
/// 4. Loads the return value from the appropriate State field
llvm::Function *createNativeWrapper(llvm::Function *lifted_fn,
                                     const FunctionABI &abi,
                                     const StateFieldMap &field_map,
                                     llvm::StructType *state_ty) {
  auto &M = *lifted_fn->getParent();
  auto &Ctx = M.getContext();

  bool is_public_output_root = isPublicOutputRoot(lifted_fn);
  FunctionABI wrapper_abi = abi;
  if (is_public_output_root && !wrapper_abi.ret.has_value()) {
    if (auto rax = field_map.fieldByName("RAX"); rax.has_value()) {
      wrapper_abi.ret = RecoveredReturn{
          "RAX",
          rax->offset,
          8,
          false,
      };
    } else if (auto x0 = field_map.fieldByName("X0"); x0.has_value()) {
      wrapper_abi.ret = RecoveredReturn{
          "X0",
          x0->offset,
          8,
          false,
      };
    }
  }
  unsigned gpr_param_count =
      exportedRootGPRParamCount(wrapper_abi, is_public_output_root);
  auto public_root_forced_gpr_constants =
      is_public_output_root
          ? detectPublicRootForcedGPRPrefixConstants(*lifted_fn, wrapper_abi,
                                                     gpr_param_count)
          : llvm::SmallVector<std::optional<uint64_t>, 2>{};
  auto public_root_extra_gpr_seeds =
      is_public_output_root
          ? detectPublicRootExtraGPRSeeds(*lifted_fn, wrapper_abi)
          : llvm::DenseMap<unsigned, EntrySeedValue>{};
  auto public_root_hidden_nonparam_gpr_seeds =
      is_public_output_root
          ? detectPublicRootHiddenNonParamGPRSeeds(*lifted_fn, wrapper_abi,
                                                   field_map)
          : llvm::DenseMap<unsigned, EntrySeedValue>{};
  auto public_root_driver_seed_exprs =
      is_public_output_root
          ? collectDriverProvidedPublicRootSeedExprs(*lifted_fn)
          : DriverSeedExprMap{};
  if (is_public_output_root && debugPublicRootSeeds()) {
    llvm::errs() << "[public-root-seeds] " << lifted_fn->getName()
                 << " extra_gpr_live_ins=" << abi.extra_gpr_live_ins.size()
                 << " extra_seeds=" << public_root_extra_gpr_seeds.size()
                 << " hidden_nonparam_seeds="
                 << public_root_hidden_nonparam_gpr_seeds.size()
                 << " driver_seed_exprs="
                 << public_root_driver_seed_exprs.size() << "\n";
    for (unsigned off : abi.extra_gpr_live_ins) {
      llvm::errs() << "  off=" << off;
      auto it = public_root_extra_gpr_seeds.find(off);
      if (it == public_root_extra_gpr_seeds.end()) {
        llvm::errs() << " seed=<none>\n";
        continue;
      }
      llvm::errs() << " seed="
                   << (it->second.kind == EntrySeedValue::Kind::Constant
                           ? "const"
                           : "pc+")
                   << it->second.value << "\n";
    }
    for (const auto &[off, seed] : public_root_hidden_nonparam_gpr_seeds) {
      llvm::errs() << "  hidden_off=" << off << " seed="
                   << (seed.kind == EntrySeedValue::Kind::Constant ? "const"
                                                                   : "pc+")
                   << seed.value << "\n";
    }
    for (const auto &[reg_name, expr] : public_root_driver_seed_exprs) {
      llvm::errs() << "  driver_seed " << reg_name << "=";
      if (!expr) {
        llvm::errs() << "<null>\n";
        continue;
      }
      switch (expr->kind) {
        case DriverSeedExpr::Kind::Param:
          llvm::errs() << "param";
          break;
        case DriverSeedExpr::Kind::Constant:
          llvm::errs() << "const";
          break;
        case DriverSeedExpr::Kind::Add64:
          llvm::errs() << "add64";
          break;
        case DriverSeedExpr::Kind::Xor64:
          llvm::errs() << "xor64";
          break;
        case DriverSeedExpr::Kind::Xor32:
          llvm::errs() << "xor32";
          break;
        case DriverSeedExpr::Kind::And32:
          llvm::errs() << "and32";
          break;
        case DriverSeedExpr::Kind::ZExt32:
          llvm::errs() << "zext32";
          break;
        case DriverSeedExpr::Kind::Rol64:
          llvm::errs() << "rol64";
          break;
        case DriverSeedExpr::Kind::Ror64:
          llvm::errs() << "ror64";
          break;
      }
      llvm::errs() << "\n";
    }
  }
  const unsigned exposed_gpr_param_count =
      gpr_param_count - public_root_forced_gpr_constants.size();
  auto *native_ty = buildNativeType(wrapper_abi, Ctx, is_public_output_root,
                                    exposed_gpr_param_count,
                                    is_public_output_root,
                                    false);

  // Name: lifted function name + "_native"
  std::string native_name = nativeWrapperName(*lifted_fn);
  auto *native_fn = llvm::Function::Create(
      native_ty, llvm::Function::ExternalLinkage, native_name, M);
  native_fn->addFnAttr(llvm::Attribute::MustProgress);
  native_fn->addFnAttr(llvm::Attribute::NoUnwind);
  // Propagate VM handler metadata so downstream passes preserve exact richardvm
  // identity across ABI wrapper generation.
  if (lifted_fn->hasFnAttribute("omill.vm_handler"))
    native_fn->addFnAttr("omill.vm_handler");
  if (lifted_fn->hasFnAttribute("omill.vm_wrapper"))
    native_fn->addFnAttr("omill.vm_wrapper");
  auto propagateStringAttr = [&](llvm::StringRef name) {
    auto attr = lifted_fn->getFnAttribute(name);
    if (attr.isValid() && attr.isStringAttribute())
      native_fn->addFnAttr(name, attr.getValueAsString());
  };
  propagateStringAttr("omill.vm_trace_in_hash");
  propagateStringAttr("omill.vm_demerged_clone");
  propagateStringAttr("omill.vm_outlined_virtual_call");
  propagateStringAttr("omill.vm_helper_hash");
  propagateStringAttr("omill.vm_helper_caller");
  propagateStringAttr("omill.vm_virtual_callee_kind");
  propagateStringAttr("omill.vm_virtual_callee_base");
  propagateStringAttr("omill.vm_virtual_callee_round");
  propagateStringAttr("omill.vm_handler_va");
  propagateStringAttr("omill.vm_trace_hash");
  propagateStringAttr("omill.trace_native_target");
  propagateStringAttr("omill.export_entry_seed_exprs");
  propagateStringAttr("omill.export_callsite_win64_gpr_count");
  propagateStringAttr("omill.internal_output_root");
  if (native_fn->getFnAttribute("omill.vm_demerged_clone").isValid() ||
      native_fn->getFnAttribute("omill.vm_outlined_virtual_call").isValid() ||
      native_fn->getFnAttribute("omill.trace_native_target").isValid()) {
    native_fn->addFnAttr(llvm::Attribute::NoInline);
  }
  if (lifted_fn->hasFnAttribute("omill.vm_entry_seed"))
    native_fn->addFnAttr("omill.vm_entry_seed");
  if (lifted_fn->hasFnAttribute("omill.output_root"))
    native_fn->addFnAttr("omill.output_root");
  if (lifted_fn->hasFnAttribute("omill.closed_root_slice"))
    native_fn->addFnAttr("omill.closed_root_slice", "1");
  if (lifted_fn->hasFnAttribute("omill.closed_root_slice_root"))
    native_fn->addFnAttr("omill.closed_root_slice_root", "1");

  auto *entry = llvm::BasicBlock::Create(Ctx, "entry", native_fn);
  llvm::IRBuilder<> Builder(entry);
  const uint64_t entry_va = extractEntryVA(lifted_fn->getName());

  // If we can't find the State type, create a raw byte allocation.
  llvm::Value *state_alloca;
  if (state_ty) {
    state_alloca = Builder.CreateAlloca(state_ty, nullptr, "state");
    // Zero-init the state
    auto state_size = M.getDataLayout().getTypeAllocSize(state_ty);
    Builder.CreateMemSet(state_alloca, Builder.getInt8(0), state_size,
                          llvm::MaybeAlign(16));
  } else {
    // Fallback: allocate raw bytes (4096 is generous for x86_64 State).
    auto *raw_ty = llvm::ArrayType::get(Builder.getInt8Ty(), 4096);
    state_alloca = Builder.CreateAlloca(raw_ty, nullptr, "state_raw");
    Builder.CreateMemSet(state_alloca, Builder.getInt8(0), 4096,
                          llvm::MaybeAlign(16));
  }

  // Seed a synthetic native stack so lifted prologues don't run with SP=0.
  // Keeping SP as a dynamic pointer avoids constant-folding stack math into
  // degenerate infinite loops in flattened dispatchers.
  constexpr uint64_t kSyntheticStackSize = 1ull << 16;  // 64 KiB
  // Extra room above SP for caller-frame reads (e.g. RSP+456 in
  // sub_1402d4b7e).  Without this, positive SP-relative loads fall
  // outside the alloca → OOB UB → optimizer folds body to unreachable.
  constexpr uint64_t kCallerFrameRoom = 0x1000;  // 4 KiB
  constexpr uint64_t kTotalStackSize = kSyntheticStackSize + kCallerFrameRoom;
  auto *stack_ty =
      llvm::ArrayType::get(Builder.getInt8Ty(), kTotalStackSize);
  auto *stack_alloca = Builder.CreateAlloca(stack_ty, nullptr, "native_stack");
  // Fill with 0xCC so reads from caller-frame offsets yield a definite
  // non-null/non-zero value instead of undef.  inttoptr(0xCC..CC) is not
  // UB, so the optimizer won't collapse the function body to unreachable.
  Builder.CreateMemSet(stack_alloca, Builder.getInt8(0xCC),
                        kTotalStackSize, llvm::MaybeAlign(16));
  auto *stack_top = Builder.CreateConstGEP1_64(
      Builder.getInt8Ty(), stack_alloca, kSyntheticStackSize - 0x20);
  auto *stack_top_i64 = Builder.CreatePtrToInt(stack_top, Builder.getInt64Ty());
  // Seed the stack pointer register (RSP for x86-64, sp for AArch64).
  for (const char *sp_name : {"RSP", "SP", "sp"}) {
    if (auto sp = field_map.fieldByName(sp_name); sp.has_value()) {
      auto *sp_ptr = buildStateGEP(Builder, state_alloca, sp->offset);
      Builder.CreateStore(stack_top_i64, sp_ptr);
      break;
    }
  }
  // Seed the frame pointer register (RBP for x86-64, x29 for AArch64).
  for (const char *fp_name : {"RBP", "FP", "x29", "X29"}) {
    if (auto fp = field_map.fieldByName(fp_name); fp.has_value()) {
      auto *fp_ptr = buildStateGEP(Builder, state_alloca, fp->offset);
      Builder.CreateStore(stack_top_i64, fp_ptr);
      break;
    }
  }

  if (is_public_output_root) {
    // Hidden VM-only GPR live-ins on exported roots are internal scaffolding,
    // not part of the public ABI. Seed them from the synthetic stack so
    // inlined VM bookkeeping does not collapse into inttoptr(low-constant)
    // artifacts like inttoptr(400).
    for (unsigned off : abi.extra_gpr_live_ins) {
      auto *field_ptr = buildStateGEP(Builder, state_alloca, off);
      if (auto it = public_root_extra_gpr_seeds.find(off);
          it != public_root_extra_gpr_seeds.end()) {
        uint64_t seed_value = 0;
        switch (it->second.kind) {
          case EntrySeedValue::Kind::Constant:
            seed_value = static_cast<uint64_t>(it->second.value);
            break;
          case EntrySeedValue::Kind::ProgramCounterRelative:
            seed_value =
                static_cast<uint64_t>(static_cast<int64_t>(entry_va) +
                                      it->second.value);
            break;
        }
        Builder.CreateStore(Builder.getInt64(seed_value), field_ptr);
      } else {
        Builder.CreateStore(stack_top_i64, field_ptr);
      }
    }

    for (const auto &[off, seed] : public_root_hidden_nonparam_gpr_seeds) {
      auto *field_ptr = buildStateGEP(Builder, state_alloca, off);
      uint64_t seed_value = 0;
      switch (seed.kind) {
        case EntrySeedValue::Kind::Constant:
          seed_value = static_cast<uint64_t>(seed.value);
          break;
        case EntrySeedValue::Kind::ProgramCounterRelative:
          seed_value =
              static_cast<uint64_t>(static_cast<int64_t>(entry_va) +
                                    seed.value);
          break;
      }
      Builder.CreateStore(Builder.getInt64(seed_value), field_ptr);
    }

    auto get_public_root_param_value = [&](unsigned param_index)
        -> llvm::Value * {
      if (param_index < public_root_forced_gpr_constants.size()) {
        return Builder.getInt64(*public_root_forced_gpr_constants[param_index]);
      }

      unsigned arg_index = 0;
      for (unsigned i = 0; i < param_index; ++i) {
        if (i < public_root_forced_gpr_constants.size())
          continue;
        ++arg_index;
      }
      if (arg_index >= native_fn->arg_size())
        return Builder.getInt64(0);
      auto *arg = native_fn->getArg(arg_index);
      if (arg->getType()->isPointerTy()) {
        return Builder.CreatePtrToInt(arg, Builder.getInt64Ty(),
                                      arg->getName() + ".i64");
      }
      return arg;
    };

    for (const auto &[reg_name, expr] : public_root_driver_seed_exprs) {
      auto field = field_map.fieldByName(reg_name);
      if (!field.has_value())
        continue;
      auto *field_ptr = buildStateGEP(Builder, state_alloca, field->offset);
      auto *value =
          evaluateDriverSeedExpr(*expr, Builder, get_public_root_param_value);
      Builder.CreateStore(value, field_ptr);
    }
  }

  // Store GPR parameters into State fields.
  unsigned native_gpr_arg_index = 0;
  for (unsigned i = 0; i < gpr_param_count; ++i) {
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.params[i].state_offset);
    if (i < public_root_forced_gpr_constants.size()) {
      Builder.CreateStore(
          Builder.getInt64(*public_root_forced_gpr_constants[i]), field_ptr);
      continue;
    }

    auto *param = native_fn->getArg(native_gpr_arg_index++);
    llvm::Value *param_i64 = param;
    if (param->getType()->isPointerTy()) {
      param_i64 = Builder.CreatePtrToInt(param, Builder.getInt64Ty(),
                                         param->getName() + ".i64");
    }
    Builder.CreateStore(param_i64, field_ptr);
  }

  // Store stack-passed parameters to the caller's stack area.
  // In the native wrapper, we need to store them at the appropriate
  // SP-relative offsets so the lifted function can read them.
  auto sp_field = field_map.fieldByName("RSP");
  if (!sp_field) sp_field = field_map.fieldByName("SP");
  if (!sp_field) sp_field = field_map.fieldByName("sp");
  if (!is_public_output_root && sp_field.has_value()) {
    auto rsp = sp_field;
    for (unsigned i = 0; i < wrapper_abi.numStackParams(); ++i) {
      unsigned arg_idx = gpr_param_count + i;
      auto *param = native_fn->getArg(arg_idx);
      // Store at RSP + stack_offset (the callee will load from there).
      auto *rsp_ptr = buildStateGEP(Builder, state_alloca, rsp->offset);
      auto *rsp_val = Builder.CreateLoad(Builder.getInt64Ty(), rsp_ptr, "rsp");
      auto *addr = Builder.CreateAdd(
          rsp_val, Builder.getInt64(wrapper_abi.stack_params[i].stack_offset));
      auto *ptr = Builder.CreateIntToPtr(addr,
          llvm::PointerType::get(Builder.getContext(), 0));
      Builder.CreateStore(param, ptr);
    }
  }

  // Store XMM parameters into State vector register slots.
  for (unsigned i = 0; !is_public_output_root && i < wrapper_abi.numXMMParams();
       ++i) {
    unsigned arg_idx = gpr_param_count + wrapper_abi.numStackParams() + i;
    auto *param = native_fn->getArg(arg_idx);
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.xmm_live_ins[i]);
    Builder.CreateStore(param, field_ptr);
  }

  // Store extra GPR parameters into State fields.
  for (unsigned i = 0;
       !is_public_output_root && i < wrapper_abi.numExtraGPRParams(); ++i) {
    unsigned arg_idx = gpr_param_count + wrapper_abi.numStackParams() +
                       wrapper_abi.numXMMParams() + i;
    auto *param = native_fn->getArg(arg_idx);
    auto *field_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.extra_gpr_live_ins[i]);
    Builder.CreateStore(param, field_ptr);
  }

  // Store param-to-State-offset metadata so per-callsite clone logic
  // can map native function params back to emulator GPR indices.
  {
    std::string offsets_str;
    for (unsigned i = 0; i < gpr_param_count; ++i)
      if (!(is_public_output_root &&
            i < public_root_forced_gpr_constants.size()))
      offsets_str += std::to_string(wrapper_abi.params[i].state_offset) + ",";
    for (unsigned i = 0; !is_public_output_root &&
                         i < wrapper_abi.numStackParams(); ++i)
      offsets_str += "stack,";  // Stack params don't map to GPRs.
    for (unsigned i = 0; !is_public_output_root &&
                         i < wrapper_abi.numXMMParams(); ++i)
      offsets_str += "xmm,";   // XMM params don't map to GPRs.
    for (unsigned i = 0; !is_public_output_root &&
                         i < wrapper_abi.numExtraGPRParams(); ++i)
      offsets_str += std::to_string(wrapper_abi.extra_gpr_live_ins[i]) + ",";
    if (!offsets_str.empty())
      offsets_str.pop_back();
    native_fn->addFnAttr("omill.param_state_offsets", offsets_str);
  }

  // Build arguments for the lifted function call.
  // Lifted functions have signature: (State*, i64, Memory*) -> Memory*
  auto *lifted_ty = lifted_fn->getFunctionType();
  llvm::SmallVector<llvm::Value *, 3> call_args;
  // Arg 0: State pointer.
  call_args.push_back(state_alloca);

  // Arg 1: Entry PC from the lifted symbol name (e.g. sub_401000).
  // Passing 0 here can trap unresolved dispatchers in synthetic loops.
  if (lifted_ty->getNumParams() > 1) {
    call_args.push_back(Builder.getInt64(entry_va));
  }

  // Arg 2: Memory pointer. Use null (not poison) to avoid injecting UB.
  if (lifted_ty->getNumParams() > 2) {
    call_args.push_back(
        llvm::Constant::getNullValue(lifted_ty->getParamType(2)));
  }

  Builder.CreateCall(lifted_fn, call_args);

  // Load return value(s) from State.
  if (wrapper_abi.hasStructReturn() && !is_public_output_root) {
    // Build a struct containing the primary return + clobbered callee-saved.
    auto *struct_ty = llvm::cast<llvm::StructType>(native_fn->getReturnType());
    llvm::Value *agg = llvm::PoisonValue::get(struct_ty);
    unsigned idx = 0;

    // Primary return value (RAX or XMM0), if present.
    if (wrapper_abi.ret.has_value()) {
      llvm::Type *load_ty = wrapper_abi.ret->is_vector
          ? static_cast<llvm::Type *>(
                llvm::FixedVectorType::get(Builder.getInt64Ty(), 2))
          : static_cast<llvm::Type *>(Builder.getInt64Ty());
      auto *ret_ptr = buildStateGEP(Builder, state_alloca,
                                     wrapper_abi.ret->state_offset);
      auto *primary = Builder.CreateLoad(load_ty, ret_ptr, "retval");
      agg = Builder.CreateInsertValue(agg, primary, idx++);
    }

    // Extra clobbered callee-saved values (i64 each).
    for (unsigned off : wrapper_abi.extra_gpr_live_outs) {
      auto *ptr = buildStateGEP(Builder, state_alloca, off);
      auto *val = Builder.CreateLoad(Builder.getInt64Ty(), ptr,
                                     "clobbered." + llvm::Twine(off));
      agg = Builder.CreateInsertValue(agg, val, idx++);
    }

    Builder.CreateRet(agg);
  } else if (wrapper_abi.ret.has_value()) {
    auto *ret_ptr = buildStateGEP(Builder, state_alloca,
                                   wrapper_abi.ret->state_offset);
    llvm::Type *load_ty;
    if (wrapper_abi.ret->is_vector) {
      load_ty = llvm::FixedVectorType::get(Builder.getInt64Ty(), 2);
    } else {
      load_ty = Builder.getInt64Ty();
    }
    auto *ret_val = Builder.CreateLoad(load_ty, ret_ptr, "retval");
    Builder.CreateRet(ret_val);
  } else {
    Builder.CreateRetVoid();
  }

  return native_fn;
}

bool rewritePublicRootNativeHelperCallArgs(llvm::Function &F,
                                           const StateFieldMap &field_map) {
  if (!F.hasFnAttribute("omill.output_root"))
    return false;

  auto root_param_offsets = collectParamStateOffsets(F);
  if (root_param_offsets.empty())
    return false;

  auto driver_seed_exprs = collectDriverProvidedPublicRootSeedExprs(F);
  if (driver_seed_exprs.empty())
    return false;

  llvm::DenseMap<unsigned, unsigned> root_offset_to_arg_index;
  unsigned arg_index = 0;
  for (auto offset : root_param_offsets) {
    if (!offset.has_value())
      continue;
    if (arg_index >= F.arg_size())
      break;
    root_offset_to_arg_index.insert({*offset, arg_index++});
  }

  bool changed = false;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *CB = llvm::dyn_cast<llvm::CallBase>(&I);
      if (!CB)
        continue;
      auto *callee = CB->getCalledFunction();
      if (!callee || callee->isDeclaration() || callee == &F)
        continue;

      auto callee_param_offsets = collectParamStateOffsets(*callee);
      if (callee_param_offsets.empty() ||
          callee_param_offsets.size() != CB->arg_size())
        continue;

      llvm::IRBuilder<> Builder(CB);
      auto getRootParamValue = [&](unsigned param_index) -> llvm::Value * {
        if (param_index >= F.arg_size())
          return Builder.getInt64(0);
        auto *arg = F.getArg(param_index);
        if (arg->getType()->isPointerTy()) {
          return Builder.CreatePtrToInt(arg, Builder.getInt64Ty(),
                                        arg->getName() + ".i64");
        }
        return arg;
      };

      auto expressionForOffset = [&](unsigned offset) -> llvm::Value * {
        if (auto it = root_offset_to_arg_index.find(offset);
            it != root_offset_to_arg_index.end()) {
          return getRootParamValue(it->second);
        }

        for (const auto &[reg_name, expr] : driver_seed_exprs) {
          auto field = field_map.fieldByName(reg_name);
          if (!field.has_value() || field->offset != offset)
            continue;
          return evaluateDriverSeedExpr(*expr, Builder, getRootParamValue);
        }
        return nullptr;
      };

      for (unsigned i = 0; i < callee_param_offsets.size(); ++i) {
        auto offset = callee_param_offsets[i];
        if (!offset.has_value())
          continue;
        auto *replacement = expressionForOffset(*offset);
        if (!replacement)
          continue;
        auto *current = CB->getArgOperand(i);
        if (replacement->getType() != current->getType()) {
          if (current->getType()->isPointerTy()) {
            replacement = Builder.CreateIntToPtr(
                replacement, current->getType(),
                callee->getName() + ".arg.ptr");
          } else if (replacement->getType()->isPointerTy() &&
                     current->getType()->isIntegerTy()) {
            replacement = Builder.CreatePtrToInt(
                replacement, current->getType(),
                callee->getName() + ".arg.int");
          } else if (replacement->getType()->isIntegerTy() &&
                     current->getType()->isIntegerTy()) {
            replacement =
                Builder.CreateIntCast(replacement, current->getType(), false);
          } else {
            continue;
          }
        }
        if (replacement == current)
          continue;
        CB->setArgOperand(i, replacement);
        changed = true;
      }
    }
  }

  return changed;
}

}  // namespace

llvm::PreservedAnalyses RecoverFunctionSignaturesPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  auto &cc_info = MAM.getResult<CallingConventionAnalysis>(M);
  StateFieldMap field_map(M);

  bool changed = false;

  // Collect lifted functions to process (avoid iterator invalidation).
  // Lifted functions have the remill signature: (ptr, i64, ptr) -> ptr
  llvm::SmallVector<llvm::Function *, 16> functions;
  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;
    if (!shouldRecoverClosedRootSliceFunction(F))
      continue;
    if (isTerminalMissingBlockStub(F))
      continue;
    functions.push_back(&F);
  }

  // Look up the State struct type once (getIdentifiedStructTypes is expensive).
  llvm::StructType *state_ty = llvm::StructType::getTypeByName(
      M.getContext(), "struct.State");

  for (auto *F : functions) {
    if (auto *existing = M.getFunction(nativeWrapperName(*F));
        existing && !existing->isDeclaration()) {
      continue;
    }
    auto *abi = cc_info.getABI(F);
    if (!abi) {
      if (getenv("OMILL_DEBUG_REWRITE"))
        llvm::errs() << "[Sigs] No ABI for " << F->getName() << "\n";
      continue;
    }
    if (getenv("OMILL_DEBUG_REWRITE"))
      llvm::errs() << "[Sigs] Creating wrapper for " << F->getName()
                    << " params=" << abi->numParams()
                    << " ret=" << abi->ret.has_value() << "\n";
    createNativeWrapper(F, *abi, field_map, state_ty);
    changed = true;
  }

  for (auto &F : M) {
    if (F.isDeclaration())
      continue;
    if (!F.getName().ends_with("_native"))
      continue;
    changed |= rewritePublicRootNativeHelperCallArgs(F, field_map);
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
