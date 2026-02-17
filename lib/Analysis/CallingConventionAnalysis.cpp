#include "omill/Analysis/CallingConventionAnalysis.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

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
                     llvm::DenseSet<unsigned> &live_out) {
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

  llvm::DenseSet<unsigned> live_in, live_out;
  computeLiveness(F, DL, live_in, live_out);

  // Win64 detection: check parameter registers RCX, RDX, R8, R9.
  unsigned win64_score = scoreWin64Params(live_in, field_map);

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

  // Return value: RAX for integer, XMM0 for float (check RAX first).
  auto rax_field = field_map.fieldByName("RAX");
  if (rax_field && live_out.count(rax_field->offset)) {
    RecoveredReturn ret;
    ret.reg_name = "RAX";
    ret.state_offset = rax_field->offset;
    ret.size = rax_field->size;
    abi.ret = ret;
  }

  // Detect XMM/vector live-ins.  Collect the base offset of each vector
  // register that is live-in so the native wrapper can accept them as extra
  // <2 x i64> parameters.
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

    // Fallback: if the StateFieldMap didn't have an entry for this offset,
    // check if it falls within the vec array region of the x86-64 State
    // struct (offset 16..16+32*64=2064, lower 16 bytes of each 64-byte
    // VectorReg slot).
    if (!field && !is_vec && off >= 16 && off < 2064) {
      unsigned vreg_idx = (off - 16) / 64;
      unsigned base = 16 + vreg_idx * 64;
      if (off < base + 16) {
        is_vec = true;
        vreg_base = base;
      }
    }

    if (is_vec && seen_vreg_bases.insert(vreg_base).second) {
      abi.xmm_live_ins.push_back(vreg_base);
      abi.has_non_standard_regs = true;
    }
  }

  // Sort XMM live-ins by offset for deterministic parameter ordering.
  llvm::sort(abi.xmm_live_ins);

  // Detect extra GPR live-ins (callee-saved regs read before written).
  // These are GPR offsets in live_in that are NOT standard Win64 params.
  {
    llvm::DenseSet<unsigned> standard_param_offsets;
    for (auto &p : abi.params)
      standard_param_offsets.insert(p.state_offset);

    for (auto off : live_in) {
      // Skip already-covered standard params.
      if (standard_param_offsets.count(off))
        continue;
      // Check if this is a GPR field.
      auto field = field_map.fieldAtOffset(off);
      if (field && field->category == StateFieldCategory::kGPR &&
          field->size == 8) {
        // Exclude RSP (stack pointer) and RIP (program counter) —
        // these are handled specially, not as params.
        if (field->name != "RSP" && field->name != "RIP") {
          abi.extra_gpr_live_ins.push_back(off);
          abi.has_non_standard_regs = true;
        }
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

  return result;
}

}  // namespace omill
