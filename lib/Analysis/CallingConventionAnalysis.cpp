#include "omill/Analysis/CallingConventionAnalysis.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <algorithm>

#include "omill/Utils/LiftedNames.h"
#include "omill/Utils/StateFieldMap.h"

namespace omill {

llvm::AnalysisKey CallingConventionAnalysis::Key;

namespace {

/// Win64 ABI: integer/pointer parameter registers, in order.
static constexpr const char *kWin64ParamRegs[] = {
    "RCX", "RDX", "R8", "R9",
};
static constexpr unsigned kWin64ParamCount = 4;

/// Win64 callee-saved (nonvolatile) registers.
static constexpr const char *kWin64CalleeSaved[] = {
    "RBX", "RBP", "RDI", "RSI", "R12", "R13", "R14", "R15",
};
static constexpr unsigned kWin64CalleeSavedCount =
    sizeof(kWin64CalleeSaved) / sizeof(kWin64CalleeSaved[0]);

/// Win64 shadow space size: 32 bytes (4 x 8) reserved by caller.
static constexpr unsigned kWin64ShadowSpaceSize = 32;

/// Resolve a pointer to its State byte offset. Returns -1 if not resolvable.
int64_t resolveStateOffset(llvm::Value *ptr, const llvm::DataLayout &DL) {
  int64_t total_offset = 0;
  llvm::Value *base = ptr;

  while (true) {
    if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
      llvm::APInt ap_offset(64, 0);
      if (GEP->accumulateConstantOffset(DL, ap_offset)) {
        total_offset += ap_offset.getSExtValue();
        base = GEP->getPointerOperand();
        continue;
      }
      return -1;
    }
    if (auto *BC = llvm::dyn_cast<llvm::BitCastOperator>(base)) {
      base = BC->getOperand(0);
      continue;
    }
    break;
  }

  if (auto *arg = llvm::dyn_cast<llvm::Argument>(base)) {
    if (arg->getArgNo() == 0 && total_offset >= 0) {
      return total_offset;
    }
  }
  return -1;
}

/// Compute live-in and live-out State field offsets for a function.
void computeLiveness(llvm::Function &F, const llvm::DataLayout &DL,
                     llvm::DenseSet<unsigned> &live_in,
                     llvm::DenseSet<unsigned> &live_out,
                     llvm::DenseSet<unsigned> &entry_live_in) {
  llvm::DenseSet<unsigned> ever_written;
  llvm::DenseSet<unsigned> written_in_entry;

  // Entry block: precise tracking of read-before-write
  if (!F.empty()) {
    for (auto &I : F.getEntryBlock()) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u = static_cast<unsigned>(off);
          if (!written_in_entry.count(u)) {
            live_in.insert(u);
            entry_live_in.insert(u);
          }
        }
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u = static_cast<unsigned>(off);
          written_in_entry.insert(u);
          ever_written.insert(u);
        }
      }
    }
  }

  // Remaining blocks: conservatively add reads not covered by entry writes
  for (auto &BB : F) {
    if (&BB == &F.getEntryBlock()) continue;
    for (auto &I : BB) {
      if (auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I)) {
        int64_t off = resolveStateOffset(LI->getPointerOperand(), DL);
        if (off >= 0) {
          unsigned u = static_cast<unsigned>(off);
          if (!written_in_entry.count(u)) {
            live_in.insert(u);
          }
        }
      }
      if (auto *SI = llvm::dyn_cast<llvm::StoreInst>(&I)) {
        int64_t off = resolveStateOffset(SI->getPointerOperand(), DL);
        if (off >= 0) {
          ever_written.insert(static_cast<unsigned>(off));
        }
      }
    }
  }

  live_out = ever_written;
}

void addFieldOffsetIfPresent(const StateFieldMap &field_map,
                             llvm::StringRef name,
                             llvm::DenseSet<unsigned> &offsets) {
  if (auto field = field_map.fieldByName(name); field.has_value()) {
    offsets.insert(field->offset);
  }
}

llvm::DenseSet<unsigned> collectWin64ParamRegisterOffsets(
    const StateFieldMap &field_map) {
  llvm::DenseSet<unsigned> offsets;

  // Include common aliases because remill naming can vary by module
  // (e.g. RCX vs CL, R8 vs R8D).
  static constexpr const char *kParamRegAliases[] = {
      "RCX", "ECX", "CX", "CL",
      "RDX", "EDX", "DX", "DL",
      "R8",  "R8D", "R8W", "R8B",
      "R9",  "R9D", "R9W", "R9B",
  };
  for (auto *name : kParamRegAliases) {
    addFieldOffsetIfPresent(field_map, name, offsets);
  }

  return offsets;
}

/// Count how many consecutive Win64 parameter registers are live-in.
unsigned scoreWin64Params(const llvm::DenseSet<unsigned> &live_in,
                          const StateFieldMap &field_map) {
  unsigned matched = 0;
  for (unsigned i = 0; i < kWin64ParamCount; ++i) {
    auto field = field_map.fieldByName(kWin64ParamRegs[i]);
    if (!field) break;
    if (live_in.count(field->offset)) {
      matched++;
    } else {
      break;
    }
  }
  return matched;
}

FunctionABI analyzeFunction(llvm::Function &F, const llvm::DataLayout &DL,
                            const StateFieldMap &field_map) {
  FunctionABI abi;

  if (F.isDeclaration() || F.empty()) return abi;
  if (F.arg_size() == 0) return abi;

  llvm::DenseSet<unsigned> live_in, live_out, entry_live_in;
  computeLiveness(F, DL, live_in, live_out, entry_live_in);

  // Win64 detection: use entry-block read-before-write signals only.
  // Non-entry reads are often transformed temporaries, not true ABI params.
  unsigned win64_score = scoreWin64Params(entry_live_in, field_map);

  if (win64_score > 0) {
    abi.cc = DetectedCC::kWin64;

    // Build parameter list
    for (unsigned i = 0; i < win64_score; ++i) {
      auto field = field_map.fieldByName(kWin64ParamRegs[i]);
      if (!field) break;

      RecoveredParam param;
      param.reg_name = kWin64ParamRegs[i];
      param.state_offset = field->offset;
      param.size = field->size;
      param.index = i;
      abi.params.push_back(param);
    }
  } else {
    // No parameter registers detected in the entry block.  For obfuscated
    // functions (SSE mutation entry), the liveness scan misses GPR reads.
    // Default to Win64 with all 4 params — unused params become dead values
    // after inlining and are trivially eliminated by DCE.
    abi.cc = DetectedCC::kWin64;
    for (unsigned i = 0; i < kWin64ParamCount; ++i) {
      auto field = field_map.fieldByName(kWin64ParamRegs[i]);
      if (!field) break;
      RecoveredParam param;
      param.reg_name = kWin64ParamRegs[i];
      param.state_offset = field->offset;
      param.size = field->size;
      param.index = i;
      abi.params.push_back(param);
    }
  }

  // Return value: RAX for integer, XMM0 for float.
  // Check RAX first (most common); fall back to XMM0 if RAX is not live-out.
  auto rax_field = field_map.fieldByName("RAX");
  if (rax_field && live_out.count(rax_field->offset)) {
    RecoveredReturn ret;
    ret.reg_name = "RAX";
    ret.state_offset = rax_field->offset;
    ret.size = rax_field->size;
    ret.is_vector = false;
    abi.ret = ret;
  } else {
    // XMM0 return: Win64 returns floats/doubles in XMM0 (first vector reg).
    // Use the field map to find vector registers dynamically.
    for (auto off : live_out) {
      auto field = field_map.fieldAtOffset(off);
      if (!field)
        continue;
      if (field->category != StateFieldCategory::kVector)
        continue;
      // Only XMM0 can be a return register.  Check if this is the first
      // vector register base (offset within the first 64-byte VectorReg).
      // VectorReg[0] base is the field's parent offset.
      unsigned vreg_idx = 0;
      if (off >= 16 && off < 2064)
        vreg_idx = (off - 16) / 64;
      if (vreg_idx == 0) {
        RecoveredReturn ret;
        ret.reg_name = "XMM0";
        ret.state_offset = field->offset;
        ret.size = 16;
        ret.is_vector = true;
        abi.ret = ret;
        break;
      }
    }
  }

  // Detect XMM/vector live-ins.  In Win64 ABI, only XMM0-XMM3 can be
  // parameters (positions 0-3), and each position uses EITHER a GPR or an
  // XMM register, never both.  XMM4+ are scratch/callee-saved, never params.
  //
  // Only consider XMM params for positions within the detected param count.
  // If scoreWin64Params detected N consecutive GPR params, the function has
  // N parameter slots.  XMM at positions >= N would imply additional params
  // that the GPR analysis didn't find — in our PE decompilation context,
  // these are obfuscation artifacts (vectorized integer ops), not real float
  // parameters.
  llvm::DenseSet<unsigned> filled_param_positions;
  for (auto &p : abi.params) {
    filled_param_positions.insert(p.index);
  }

  static constexpr unsigned kMaxXMMParams = 4;

  llvm::DenseSet<unsigned> seen_vreg_bases;
  for (auto off : live_in) {
    bool is_vec = false;
    unsigned vreg_base = 0;

    // Check StateFieldMap first.
    auto field = field_map.fieldAtOffset(off);
    if (field && field->category == StateFieldCategory::kVector) {
      is_vec = true;
      vreg_base = field->offset;
    }

    // Fallback: check if offset falls within the vec array region.
    if (!field && !is_vec && off >= 16 && off < 2064) {
      unsigned vreg_idx = (off - 16) / 64;
      unsigned base = 16 + vreg_idx * 64;
      if (off < base + 16) {
        is_vec = true;
        vreg_base = base;
      }
    }

    if (!is_vec)
      continue;
    if (!seen_vreg_bases.insert(vreg_base).second)
      continue;

    // Only XMM0-3 can be Win64 parameters.  Skip XMM4+.
    unsigned xmm_idx = (vreg_base - 16) / 64;
    if (xmm_idx >= kMaxXMMParams)
      continue;

    // Only consider XMM at positions within the detected GPR param count.
    // Positions beyond the GPR count are not real params — they're artifacts.
    if (xmm_idx >= win64_score)
      continue;

    // If the corresponding GPR param position is already filled,
    // this XMM is scratch, not a parameter.
    if (filled_param_positions.count(xmm_idx))
      continue;

    abi.xmm_live_ins.push_back(vreg_base);
    abi.has_non_standard_regs = true;
  }

  // Sort XMM live-ins by offset for deterministic parameter ordering.
  llvm::sort(abi.xmm_live_ins);

  // Detect extra GPR live-ins: only volatile (caller-saved) GPRs beyond the
  // standard parameter registers.  Callee-saved registers (RBX, RBP, RDI,
  // RSI, R12-R15) are preserved by convention — they are NOT input params
  // even if the function reads them (it reads them to save/restore).
  // Also exclude RSP and RIP which are handled specially.
  {
    llvm::DenseSet<unsigned> standard_param_offsets;
    for (auto &p : abi.params)
      standard_param_offsets.insert(p.state_offset);

    // Build set of offsets to exclude: standard params + callee-saved +
    // RSP/RIP + volatile scratch (RAX=return, R10/R11=scratch).
    // In Win64, only RCX/RDX/R8/R9 can be params, and those are already
    // handled as standard params.  Exclude param-register offsets explicitly
    // too, since some modules use alias names (e.g. R8D) that can evade the
    // standard-param map and appear as false "extra" GPRs.
    // All other GPRs are either callee-saved,
    // return value, stack pointer, program counter, or scratch.
    llvm::DenseSet<unsigned> excluded_offsets = standard_param_offsets;
    auto win64_param_offsets = collectWin64ParamRegisterOffsets(field_map);
    excluded_offsets.insert(win64_param_offsets.begin(),
                            win64_param_offsets.end());
    for (unsigned i = 0; i < kWin64CalleeSavedCount; ++i) {
      auto field = field_map.fieldByName(kWin64CalleeSaved[i]);
      if (field)
        excluded_offsets.insert(field->offset);
    }
    static constexpr const char *kExcludedGPRs[] = {
        "RSP", "RIP", "RAX", "R10", "R11",
    };
    for (auto name : kExcludedGPRs) {
      auto field = field_map.fieldByName(name);
      if (field) excluded_offsets.insert(field->offset);
    }

    for (auto off : live_in) {
      if (excluded_offsets.count(off))
        continue;
      auto field = field_map.fieldAtOffset(off);
      if (field && field->category == StateFieldCategory::kGPR &&
          field->size == 8) {
        abi.extra_gpr_live_ins.push_back(off);
        abi.has_non_standard_regs = true;
      }
    }
    llvm::sort(abi.extra_gpr_live_ins);
  }

  // Identify clobbered callee-saved registers.
  // In Win64, RBX, RBP, RDI, RSI, R12-R15 are nonvolatile.
  for (unsigned i = 0; i < kWin64CalleeSavedCount; ++i) {
    auto field = field_map.fieldByName(kWin64CalleeSaved[i]);
    if (field && live_out.count(field->offset)) {
      abi.clobbered_callee_saved.push_back(kWin64CalleeSaved[i]);
    }
  }

  // Win64: shadow space (home area) of 32 bytes is allocated by the caller
  // at [RSP+8..RSP+40]. Store this info for stack frame recovery.
  abi.shadow_space_size = kWin64ShadowSpaceSize;

  return abi;
}

}  // namespace

/// Propagate callee XMM live-ins to callers.
///
/// When a function passes its State pointer (arg 0) to a callee, the callee's
/// XMM live-ins are effectively live-ins of the caller too — the caller must
/// have those XMM values in State for the callee to read them.
///
/// This is critical for SEH resolution: the exception function
/// (sub_140001a5a) passes State to the CFF resolver (sub_140013efa) which
/// reads XMMs.  Without propagation, the exception function's native wrapper
/// would have no XMM params and pass zeroinitializer to the resolver.
static void propagateCalleeXMMLiveIns(
    llvm::Module &M,
    llvm::DenseMap<const llvm::Function *, FunctionABI> &abis) {

  // Build VA → definition map for resolving forward declarations.
  llvm::DenseMap<uint64_t, const llvm::Function *> va_to_def;
  for (auto &[func, abi] : abis) {
    uint64_t va = extractEntryVA(func->getName());
    if (va != 0)
      va_to_def[va] = func;
  }

  // Build a map from callee definition → callers for lifted functions.
  // Only consider calls where the caller passes its own State (arg 0).
  llvm::DenseMap<const llvm::Function *,
                 llvm::SmallVector<const llvm::Function *, 4>>
      callee_to_callers;

  for (auto &F : M) {
    if (!isLiftedFunction(F) || F.isDeclaration() || F.arg_size() == 0)
      continue;
    llvm::Argument *state_arg = F.getArg(0);

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI || CI->arg_size() == 0)
          continue;
        auto *callee = CI->getCalledFunction();
        if (!callee)
          continue;
        // Check that the caller passes its own State as the first arg.
        if (CI->getArgOperand(0) != state_arg)
          continue;

        // Resolve callee to its ABI-analyzed definition.
        // isLiftedFunction() rejects declarations, so use extractEntryVA
        // to match declarations (sub_140013efa) to definitions
        // (sub_140013efa.1) by VA.
        uint64_t callee_va = extractEntryVA(callee->getName());
        if (callee_va == 0)
          continue;
        auto def_it = va_to_def.find(callee_va);
        if (def_it == va_to_def.end())
          continue;
        callee_to_callers[def_it->second].push_back(&F);
      }
    }
  }

  // Propagate: for each callee with XMM or extra GPR live-ins, merge into
  // callers.  Iterate to fixpoint (handles transitive chains A → B → C).
  bool changed = true;
  while (changed) {
    changed = false;
    for (auto &[callee, callers] : callee_to_callers) {
      auto callee_it = abis.find(callee);
      if (callee_it == abis.end())
        continue;
      auto &callee_abi = callee_it->second;

      for (auto *caller : callers) {
        auto caller_it = abis.find(caller);
        if (caller_it == abis.end())
          continue;
        auto &caller_abi = caller_it->second;

        // Merge callee's XMM live-ins into caller's.
        {
          llvm::DenseSet<unsigned> existing(caller_abi.xmm_live_ins.begin(),
                                            caller_abi.xmm_live_ins.end());
          for (unsigned off : callee_abi.xmm_live_ins) {
            if (existing.insert(off).second) {
              caller_abi.xmm_live_ins.push_back(off);
              caller_abi.has_non_standard_regs = true;
              changed = true;
            }
          }
          if (changed)
            llvm::sort(caller_abi.xmm_live_ins);
        }

        // Merge callee's extra GPR live-ins into caller's.
        {
          llvm::DenseSet<unsigned> existing(
              caller_abi.extra_gpr_live_ins.begin(),
              caller_abi.extra_gpr_live_ins.end());
          // Don't propagate offsets that are standard params for the caller.
          for (auto &p : caller_abi.params)
            existing.insert(p.state_offset);
          for (unsigned off : callee_abi.extra_gpr_live_ins) {
            if (existing.insert(off).second) {
              caller_abi.extra_gpr_live_ins.push_back(off);
              caller_abi.has_non_standard_regs = true;
              changed = true;
            }
          }
          if (changed)
            llvm::sort(caller_abi.extra_gpr_live_ins);
        }
      }
    }
  }
}

/// Win64 shadow space size (bytes).
static constexpr int64_t kShadowSpaceEnd = 0x28;  // 5th arg starts at RSP+0x28

/// Try to resolve a store pointer to a stack offset relative to RSP.
/// Returns the RSP-relative offset if the pointer is a GEP into a
/// concrete_stack alloca with omill.stack.base_offset metadata, or an
/// inttoptr(RSP + offset) pattern.
std::optional<int64_t> resolveStackOffset(llvm::Value *ptr,
                                           const llvm::DataLayout &DL) {
  // Pattern 1: GEP into concrete_stack alloca with metadata.
  if (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(ptr)) {
    llvm::APInt ap_offset(64, 0);
    if (!GEP->accumulateConstantOffset(DL, ap_offset))
      return std::nullopt;
    auto *base_alloca = llvm::dyn_cast<llvm::AllocaInst>(
        GEP->getPointerOperand()->stripPointerCasts());
    if (!base_alloca)
      return std::nullopt;
    auto *md = base_alloca->getMetadata("omill.stack.base_offset");
    if (!md || md->getNumOperands() == 0)
      return std::nullopt;
    auto *ci = llvm::mdconst::dyn_extract<llvm::ConstantInt>(
        md->getOperand(0));
    if (!ci)
      return std::nullopt;
    int64_t base_rsp_offset = ci->getSExtValue();
    int64_t gep_offset = ap_offset.getSExtValue();
    return base_rsp_offset + gep_offset;
  }

  // Pattern 2: inttoptr(add(load(State+48), const)).
  if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(ptr)) {
    auto *val = ITP->getOperand(0);
    // add(rsp_load, offset)
    if (auto *BO = llvm::dyn_cast<llvm::BinaryOperator>(val)) {
      if (BO->getOpcode() != llvm::Instruction::Add)
        return std::nullopt;
      auto *CI = llvm::dyn_cast<llvm::ConstantInt>(BO->getOperand(1));
      if (!CI)
        return std::nullopt;
      // Check if operand 0 is a load from State+48 (RSP).
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(BO->getOperand(0));
      if (!LI)
        return std::nullopt;
      int64_t state_off = resolveStateOffset(LI->getPointerOperand(), DL);
      if (state_off != 48)  // RSP offset
        return std::nullopt;
      return CI->getSExtValue();
    }
  }

  return std::nullopt;
}

/// Information about a single callsite for stack arg analysis.
struct CallsiteInfo {
  const llvm::Function *callee_def = nullptr;
  unsigned gpr_param_count = 0;
  llvm::SmallVector<int64_t, 4> stack_arg_offsets;  // RSP+offset for each
};

/// Analyze a single callsite: count register params stored and detect
/// stack arg stores in the same basic block before the call.
CallsiteInfo analyzeCallsite(llvm::CallInst *CI, const llvm::DataLayout &DL,
    const StateFieldMap &field_map,
    const llvm::DenseMap<uint64_t, const llvm::Function *> &va_to_def) {
  CallsiteInfo info;

  // Resolve callee.
  auto *callee = CI->getCalledFunction();
  if (!callee)
    return info;

  uint64_t callee_va = 0;
  if (callee->getName() == "__omill_dispatch_call" ||
      callee->getName() == "__omill_dispatch_jump") {
    // Target PC is the second arg.
    if (CI->arg_size() >= 2) {
      if (auto *pc_ci = llvm::dyn_cast<llvm::ConstantInt>(CI->getArgOperand(1)))
        callee_va = pc_ci->getZExtValue();
    }
  } else if (isLiftedFunction(*callee)) {
    callee_va = extractEntryVA(callee->getName());
  }

  if (callee_va == 0)
    return info;
  auto def_it = va_to_def.find(callee_va);
  if (def_it == va_to_def.end())
    return info;
  info.callee_def = def_it->second;

  // Walk backwards in the basic block from the call.
  auto *BB = CI->getParent();
  llvm::DenseSet<unsigned> gpr_param_offsets;

  // Collect Win64 param register offsets.
  auto win64_offsets = collectWin64ParamRegisterOffsets(field_map);

  for (auto it = CI->getReverseIterator(); it != BB->rend(); ++it) {
    auto *SI = llvm::dyn_cast<llvm::StoreInst>(&*it);
    if (!SI)
      continue;

    // Check if it's a State struct store (param register).
    int64_t state_off = resolveStateOffset(SI->getPointerOperand(), DL);
    if (state_off >= 0 && win64_offsets.count(static_cast<unsigned>(state_off))) {
      gpr_param_offsets.insert(static_cast<unsigned>(state_off));
      continue;
    }

    // Check if it's a stack store (RSP + offset >= 0x28).
    auto stack_off = resolveStackOffset(SI->getPointerOperand(), DL);
    if (stack_off && *stack_off >= kShadowSpaceEnd) {
      info.stack_arg_offsets.push_back(*stack_off);
    }
  }

  // Count consecutive GPR params.
  static constexpr const char *kParamOrder[] = {"RCX", "RDX", "R8", "R9"};
  for (unsigned i = 0; i < 4; ++i) {
    auto field = field_map.fieldByName(kParamOrder[i]);
    if (!field || !gpr_param_offsets.count(field->offset))
      break;
    info.gpr_param_count = i + 1;
  }

  // Deduplicate and sort stack arg offsets.
  llvm::sort(info.stack_arg_offsets);
  info.stack_arg_offsets.erase(
      std::unique(info.stack_arg_offsets.begin(),
                 info.stack_arg_offsets.end()),
      info.stack_arg_offsets.end());

  return info;
}

/// Refine function ABIs by analyzing callsites across the module.
/// This catches stack arguments (5th+ Win64 params) and corrects param counts
/// when the callee body analysis was imprecise due to obfuscation.
static void refineFromCallsites(
    llvm::Module &M,
    llvm::DenseMap<const llvm::Function *, FunctionABI> &abis,
    const StateFieldMap &field_map) {
  auto &DL = M.getDataLayout();

  // Build VA → definition map.
  llvm::DenseMap<uint64_t, const llvm::Function *> va_to_def;
  for (auto &[func, abi] : abis) {
    uint64_t va = extractEntryVA(func->getName());
    if (va != 0)
      va_to_def[va] = func;
  }

  // For each callee, collect callsite evidence across all callers.
  struct CalleeEvidence {
    unsigned max_gpr_params = 0;
    llvm::DenseSet<int64_t> all_stack_offsets;
  };
  llvm::DenseMap<const llvm::Function *, CalleeEvidence> evidence;

  for (auto &F : M) {
    if (F.isDeclaration() || F.arg_size() == 0)
      continue;

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *CI = llvm::dyn_cast<llvm::CallInst>(&I);
        if (!CI)
          continue;

        auto cs = analyzeCallsite(CI, DL, field_map, va_to_def);
        if (!cs.callee_def)
          continue;

        auto &ev = evidence[cs.callee_def];
        ev.max_gpr_params = std::max(ev.max_gpr_params, cs.gpr_param_count);
        for (auto off : cs.stack_arg_offsets)
          ev.all_stack_offsets.insert(off);
      }
    }
  }

  // Apply evidence to ABIs.
  for (auto &[func, ev] : evidence) {
    auto abi_it = abis.find(func);
    if (abi_it == abis.end())
      continue;
    auto &abi = abi_it->second;

    // Upgrade GPR param count if callsite evidence is stronger.
    if (ev.max_gpr_params > abi.numParams()) {
      abi.params.clear();
      for (unsigned i = 0; i < ev.max_gpr_params; ++i) {
        auto field = field_map.fieldByName(kWin64ParamRegs[i]);
        if (!field) break;
        RecoveredParam param;
        param.reg_name = kWin64ParamRegs[i];
        param.state_offset = field->offset;
        param.size = field->size;
        param.index = i;
        abi.params.push_back(param);
      }
    }

    // Add stack parameters.
    if (!ev.all_stack_offsets.empty()) {
      llvm::SmallVector<int64_t, 8> sorted_offsets(
          ev.all_stack_offsets.begin(), ev.all_stack_offsets.end());
      llvm::sort(sorted_offsets);

      for (size_t i = 0; i < sorted_offsets.size(); ++i) {
        RecoveredStackParam sp;
        sp.stack_offset = sorted_offsets[i];
        sp.size = 8;  // Win64: all stack args are 8-byte slots
        sp.index = abi.numParams() + static_cast<unsigned>(i);
        abi.stack_params.push_back(sp);
      }
    }
  }
}

CallingConventionInfo CallingConventionAnalysis::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {
  CallingConventionInfo result;
  auto &DL = M.getDataLayout();
  StateFieldMap field_map(M);

  for (auto &F : M) {
    if (!isLiftedFunction(F)) continue;

    result.function_abis[&F] = analyzeFunction(F, DL, field_map);
  }

  // Propagate callee XMM live-ins to callers (transitive closure).
  propagateCalleeXMMLiveIns(M, result.function_abis);

  // Refine ABIs with callsite evidence (stack args, param count).
  refineFromCallsites(M, result.function_abis, field_map);

  return result;
}

}  // namespace omill
