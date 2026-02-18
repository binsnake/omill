#include "omill/Passes/RecoverStackFrame.h"

#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Operator.h>

#include <algorithm>

namespace omill {

namespace {

/// Try to trace a value back to base_val + constant_offset.
/// Handles nested constant add/sub chains: add(add(base, K1), K2) → K1+K2.
bool traceToBase(llvm::Value *addr, llvm::Value *base_val, int64_t &offset,
                 unsigned depth = 0) {
  if (depth > 8) return false;
  if (addr == base_val) {
    offset = 0;
    return true;
  }

  // If base_val is a phi, also accept reaching any of its non-self incoming
  // values.  This handles the case where stores in the entry block use the
  // phi's incoming value (e.g. add(%frame_ptr, K) → inttoptr) while loads
  // in the loop use the phi itself (add(%phi, K) → inttoptr).  Both should
  // map to the same alloca.
  if (auto *base_phi = llvm::dyn_cast<llvm::PHINode>(base_val)) {
    for (unsigned i = 0; i < base_phi->getNumIncomingValues(); ++i) {
      auto *inc = base_phi->getIncomingValue(i);
      if (inc != base_phi && addr == inc) {
        offset = 0;
        return true;
      }
    }
  }

  if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(addr)) {
    auto opcode = binop->getOpcode();
    if (opcode == llvm::Instruction::Add) {
      // add(X, K) where X is derived from base_val
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
        int64_t sub_off = 0;
        if (traceToBase(binop->getOperand(0), base_val, sub_off, depth + 1)) {
          offset = sub_off + CI->getSExtValue();
          return true;
        }
      }
      // add(K, X) where X is derived from base_val
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(0))) {
        int64_t sub_off = 0;
        if (traceToBase(binop->getOperand(1), base_val, sub_off, depth + 1)) {
          offset = CI->getSExtValue() + sub_off;
          return true;
        }
      }
    }
    if (opcode == llvm::Instruction::Sub) {
      // sub(X, K) where X is derived from base_val
      if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
        int64_t sub_off = 0;
        if (traceToBase(binop->getOperand(0), base_val, sub_off, depth + 1)) {
          offset = sub_off - CI->getSExtValue();
          return true;
        }
      }
    }
  }

  return false;
}

/// Check if a value is derived from base_val through arithmetic operations,
/// phi nodes, and trunc/zext/sext casts.  Handles SROA decompose/reassemble
/// patterns and PromoteStateToSSA phi chains (with cycle detection).
bool isDerivedFrom(llvm::Value *V, llvm::Value *base_val,
                   llvm::DenseSet<llvm::Value *> &visited,
                   unsigned depth = 0) {
  if (depth > 16) return false;
  if (V == base_val) return true;

  // If base_val is a phi, also accept its non-self incoming values.
  if (auto *base_phi = llvm::dyn_cast<llvm::PHINode>(base_val)) {
    for (unsigned i = 0; i < base_phi->getNumIncomingValues(); ++i) {
      auto *inc = base_phi->getIncomingValue(i);
      if (inc != base_phi && V == inc) return true;
    }
  }

  if (!visited.insert(V).second) return false;

  if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto opcode = binop->getOpcode();
    if (opcode == llvm::Instruction::Add ||
        opcode == llvm::Instruction::Sub ||
        opcode == llvm::Instruction::Or ||
        opcode == llvm::Instruction::And ||
        opcode == llvm::Instruction::Shl ||
        opcode == llvm::Instruction::LShr ||
        opcode == llvm::Instruction::AShr) {
      return isDerivedFrom(binop->getOperand(0), base_val, visited, depth + 1) ||
             isDerivedFrom(binop->getOperand(1), base_val, visited, depth + 1);
    }
  }

  if (auto *CI = llvm::dyn_cast<llvm::CastInst>(V)) {
    auto opcode = CI->getOpcode();
    if (opcode == llvm::Instruction::Trunc ||
        opcode == llvm::Instruction::ZExt ||
        opcode == llvm::Instruction::SExt) {
      return isDerivedFrom(CI->getOperand(0), base_val, visited, depth + 1);
    }
  }

  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(V)) {
    for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
      if (isDerivedFrom(phi->getIncomingValue(i), base_val, visited, depth + 1))
        return true;
    }
  }

  return false;
}

/// Overload without explicit visited set (for callers that don't need one).
bool isDerivedFrom(llvm::Value *V, llvm::Value *base_val) {
  llvm::DenseSet<llvm::Value *> visited;
  return isDerivedFrom(V, base_val, visited, 0);
}

/// Resolve the byte offset of a GEP from the State pointer (arg0).
/// Returns -1 if the pointer doesn't originate from State.
int64_t resolveStateGEPOffset(llvm::Value *ptr, llvm::Value *state_ptr,
                              const llvm::DataLayout &DL) {
  llvm::Value *base = ptr;
  int64_t total_offset = 0;
  while (auto *GEP = llvm::dyn_cast<llvm::GEPOperator>(base)) {
    llvm::APInt ap_offset(64, 0);
    if (!GEP->accumulateConstantOffset(DL, ap_offset))
      return -1;
    total_offset += ap_offset.getSExtValue();
    base = GEP->getPointerOperand();
  }
  return (base == state_ptr) ? total_offset : -1;
}

/// Check if a value eventually reaches an inttoptr through its users,
/// following through phi nodes and binary ops (with cycle detection).
bool hasEventualIntToPtrUser(llvm::Value *V,
                             llvm::DenseSet<llvm::Value *> &visited) {
  if (!visited.insert(V).second) return false;
  for (auto *user : V->users()) {
    if (llvm::isa<llvm::IntToPtrInst>(user)) return true;
    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
      if (hasEventualIntToPtrUser(binop, visited)) return true;
    }
    if (auto *phi = llvm::dyn_cast<llvm::PHINode>(user)) {
      if (hasEventualIntToPtrUser(phi, visited)) return true;
    }
  }
  return false;
}

/// Check if a value has any constant-offset inttoptr user (directly or
/// through add/sub + inttoptr).
bool hasIntToPtrUser(llvm::Value *base) {
  for (auto *user : base->users()) {
    if (llvm::isa<llvm::IntToPtrInst>(user))
      return true;
    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
      int64_t offset = 0;
      if (traceToBase(binop, base, offset)) {
        for (auto *bu : binop->users()) {
          if (llvm::isa<llvm::IntToPtrInst>(bu))
            return true;
        }
      }
    }
  }
  return false;
}

/// Find base values for stack frame recovery.
///
/// After PromoteStateToSSA, RSP may flow through:
///   load RSP from State → add(RSP, -N) → phi → add(phi, K) → inttoptr
///
/// The pass detects this pattern and returns either the load (simple case)
/// or the phi (promoted case) as the effective base for stack accesses.
///
/// Two-pass approach:
///   1. Find State field offsets that have at least one load with a NEGATIVE
///      constant offset that eventually reaches inttoptr (through phi nodes).
///   2. Collect the effective base values: the phi (if load→add→phi pattern)
///      or the load itself (if load→add→inttoptr directly).
llvm::SmallVector<llvm::Value *, 4> findStackBaseValues(llvm::Function &F) {
  llvm::SmallVector<llvm::Value *, 4> result;

  if (F.arg_empty()) return result;
  llvm::Value *state_ptr = F.getArg(0);
  auto &DL = F.getDataLayout();

  // Pass 1: find State field offsets with negative-offset inttoptr patterns.
  // Also record the phi node (if any) that serves as the effective RSP base.
  llvm::DenseSet<int64_t> stack_field_offsets;
  // Maps State field offset → effective base (phi or load).
  llvm::DenseMap<int64_t, llvm::SmallVector<llvm::Value *, 2>> effective_bases;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64)) continue;

      int64_t state_off = resolveStateGEPOffset(
          LI->getPointerOperand(), state_ptr, DL);
      if (state_off < 0) continue;

      for (auto *user : LI->users()) {
        auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user);
        if (!binop) continue;
        int64_t offset = 0;
        if (!traceToBase(binop, LI, offset) || offset >= 0) continue;

        // Check direct inttoptr users of the add.
        bool found_direct = false;
        for (auto *bu : binop->users()) {
          if (llvm::isa<llvm::IntToPtrInst>(bu)) {
            found_direct = true;
            break;
          }
        }
        if (found_direct) {
          stack_field_offsets.insert(state_off);
          // Load is the direct base — it has inttoptr users.
          effective_bases[state_off].push_back(LI);
          break;
        }

        // Check phi users: load → add(load, -N) → phi → ... → inttoptr.
        for (auto *bu : binop->users()) {
          auto *phi = llvm::dyn_cast<llvm::PHINode>(bu);
          if (!phi) continue;
          // Check if the phi eventually reaches inttoptr.
          llvm::DenseSet<llvm::Value *> visited;
          if (hasEventualIntToPtrUser(phi, visited)) {
            stack_field_offsets.insert(state_off);
            // The phi is the effective base for stack accesses.
            effective_bases[state_off].push_back(phi);
            break;
          }
        }
        if (stack_field_offsets.count(state_off)) break;
      }
    }
  }

  if (stack_field_offsets.empty()) return result;

  // Pass 2: collect effective base values.  When a phi base exists for a
  // State field, prefer it over load bases — the phi encompasses all
  // load-based inttoptr patterns through phi-equivalent traceToBase.
  // Returning both would cause double-processing of the same inttoptr
  // instructions.
  llvm::DenseSet<int64_t> phi_fields;
  for (auto &[field_off, bases] : effective_bases) {
    for (auto *base : bases) {
      if (llvm::isa<llvm::PHINode>(base)) {
        phi_fields.insert(field_off);
        break;
      }
    }
  }

  llvm::DenseSet<llvm::Value *> seen;
  for (auto &[field_off, bases] : effective_bases) {
    bool has_phi = phi_fields.count(field_off);
    for (auto *base : bases) {
      // Skip load bases when a phi base covers the same State field.
      if (has_phi && !llvm::isa<llvm::PHINode>(base))
        continue;
      if (seen.insert(base).second) {
        if (llvm::isa<llvm::PHINode>(base) || hasIntToPtrUser(base))
          result.push_back(base);
      }
    }
  }

  // Also collect additional loads from the same State field that have
  // direct inttoptr users — but only for fields without a phi base.
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64)) continue;

      int64_t state_off = resolveStateGEPOffset(
          LI->getPointerOperand(), state_ptr, DL);
      if (state_off < 0 || !stack_field_offsets.count(state_off)) continue;
      if (phi_fields.count(state_off)) continue;

      if (seen.insert(LI).second && hasIntToPtrUser(LI))
        result.push_back(LI);
    }
  }

  return result;
}

/// Collect constant inttoptr offsets from a base value.
/// Scans all inttoptr instructions in the function to handle nested add chains.
llvm::SmallVector<int64_t, 16> collectIntToPtrOffsets(llvm::Function &F,
                                                       llvm::Value *base) {
  llvm::SmallVector<int64_t, 16> offsets;
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&I);
      if (!ITP) continue;
      int64_t offset = 0;
      if (traceToBase(ITP->getOperand(0), base, offset))
        offsets.push_back(offset);
    }
  }
  return offsets;
}

/// A contiguous region of the stack frame.
struct FrameRegion {
  int64_t min_offset;
  int64_t max_offset;
};

/// Group sorted offsets into contiguous regions.
/// Offsets within `gap` bytes of each other are in the same region.
llvm::SmallVector<FrameRegion, 4> clusterOffsets(
    llvm::SmallVector<int64_t, 16> &offsets, int64_t gap = 16) {
  llvm::SmallVector<FrameRegion, 4> regions;
  if (offsets.empty()) return regions;

  llvm::sort(offsets);
  // Remove duplicates.
  offsets.erase(std::unique(offsets.begin(), offsets.end()), offsets.end());

  int64_t cur_min = offsets[0];
  int64_t cur_max = offsets[0];

  for (size_t i = 1; i < offsets.size(); ++i) {
    if (offsets[i] - cur_max > gap) {
      regions.push_back({cur_min, cur_max});
      cur_min = offsets[i];
    }
    cur_max = offsets[i];
  }
  regions.push_back({cur_min, cur_max});
  return regions;
}

/// Collect all inttoptr instructions in the function whose operands are
/// derived from the given base value (through any arithmetic/phi chain).
llvm::SmallVector<llvm::IntToPtrInst *, 16> collectDerivedIntToPtr(
    llvm::Function &F, llvm::Value *base) {
  llvm::SmallVector<llvm::IntToPtrInst *, 16> result;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&I)) {
        if (isDerivedFrom(ITP->getOperand(0), base)) {
          result.push_back(ITP);
        }
      }
    }
  }
  return result;
}

}  // namespace

llvm::PreservedAnalyses RecoverStackFramePass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration() || F.empty() || F.arg_size() == 0) {
    return llvm::PreservedAnalyses::all();
  }

  auto base_values = findStackBaseValues(F);
  if (base_values.empty()) {
    return llvm::PreservedAnalyses::all();
  }

  llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  auto *i8_ty = EntryBuilder.getInt8Ty();
  auto *i64_ty = EntryBuilder.getInt64Ty();
  bool changed = false;

  for (auto *base : base_values) {
    // Collect all constant inttoptr offsets from this base.
    auto offsets = collectIntToPtrOffsets(F, base);
    if (offsets.empty()) continue;

    // Check if there are dynamic (non-constant) inttoptr uses of this base.
    // If so, we need to create a single alloca and RAUW the base value
    // rather than per-region allocas.
    auto all_derived = collectDerivedIntToPtr(F, base);
    bool has_dynamic_uses = false;
    for (auto *itp : all_derived) {
      int64_t off = 0;
      if (!traceToBase(itp->getOperand(0), base, off)) {
        has_dynamic_uses = true;
        break;
      }
    }

    bool is_phi_base = llvm::isa<llvm::PHINode>(base);

    if (has_dynamic_uses && is_phi_base) {
      // ---------------------------------------------------------------
      // Phi base with dynamic inttoptr uses: single alloca + RAUW phi.
      // ---------------------------------------------------------------
      llvm::sort(offsets);
      offsets.erase(std::unique(offsets.begin(), offsets.end()), offsets.end());
      int64_t min_off = offsets.front();
      int64_t max_off = offsets.back();
      int64_t frame_size = max_off - min_off + 8;
      if (frame_size <= 0) frame_size = 8;

      auto *frame_ty = llvm::ArrayType::get(i8_ty, frame_size);
      auto *frame_alloca = EntryBuilder.CreateAlloca(frame_ty, nullptr,
                                                      "stack_frame");
      frame_alloca->setAlignment(llvm::Align(16));

      // Replace constant-offset inttoptr instructions with GEP.
      auto int_to_ptrs = collectDerivedIntToPtr(F, base);
      for (auto *itp : int_to_ptrs) {
        int64_t const_off = 0;
        if (!traceToBase(itp->getOperand(0), base, const_off)) continue;
        if (const_off < min_off || const_off > max_off + 7) continue;

        llvm::IRBuilder<> Builder(itp);
        auto *gep = Builder.CreateGEP(i8_ty, frame_alloca,
            llvm::ConstantInt::get(i64_ty, const_off - min_off), "frame_ptr");
        itp->replaceAllUsesWith(gep);
        itp->eraseFromParent();
        changed = true;
      }

      // RAUW the phi with ptrtoint(alloca_base_gep) so that remaining
      // dynamic-offset inttoptr uses produce valid alloca pointers.
      // base + offset  ==>  ptrtoint(alloca) + (-min_off) + offset
      //                 ==>  inttoptr produces alloca + (offset - min_off)
      auto *gep_base = EntryBuilder.CreateGEP(i8_ty, frame_alloca,
          llvm::ConstantInt::get(i64_ty, -min_off), "frame_base");
      auto *base_int = EntryBuilder.CreatePtrToInt(gep_base, i64_ty,
                                                     "frame_base_int");
      base->replaceAllUsesWith(base_int);
      if (auto *phi = llvm::dyn_cast<llvm::PHINode>(base)) {
        phi->eraseFromParent();
      }
      changed = true;
    } else {
      // ---------------------------------------------------------------
      // Load base or phi without dynamic uses: per-region allocas.
      // ---------------------------------------------------------------
      auto regions = clusterOffsets(offsets, 16);

      for (auto &region : regions) {
        int64_t min_off = region.min_offset;
        int64_t max_off = region.max_offset;
        int64_t frame_size = max_off - min_off + 8;
        if (frame_size <= 0) frame_size = 8;

        auto *frame_ty = llvm::ArrayType::get(i8_ty, frame_size);
        auto *frame_alloca = EntryBuilder.CreateAlloca(frame_ty, nullptr,
                                                        "stack_frame");

        auto int_to_ptrs = collectDerivedIntToPtr(F, base);

        for (auto *itp : int_to_ptrs) {
          llvm::Value *operand = itp->getOperand(0);
          int64_t const_off = 0;
          if (!traceToBase(operand, base, const_off)) continue;
          if (const_off < min_off || const_off > max_off) continue;

          llvm::IRBuilder<> Builder(itp);
          auto *alloca_idx = llvm::ConstantInt::get(i64_ty,
                                                      const_off - min_off);
          auto *gep = Builder.CreateGEP(i8_ty, frame_alloca, alloca_idx,
                                         "frame_ptr");
          itp->replaceAllUsesWith(gep);
          itp->eraseFromParent();
          changed = true;
        }

        // Replace bare add(base, C) values with ptrtoint(GEP).
        {
          llvm::SmallVector<llvm::BinaryOperator *, 8> bare_ops;
          for (auto *user : base->users()) {
            auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user);
            if (!binop) continue;
            int64_t offset = 0;
            if (!traceToBase(binop, base, offset)) continue;
            if (binop->use_empty()) continue;
            if (offset < min_off || offset > max_off) continue;
            bool has_itp = false;
            for (auto *bu : binop->users()) {
              if (llvm::isa<llvm::IntToPtrInst>(bu)) { has_itp = true; break; }
            }
            if (has_itp) continue;
            bare_ops.push_back(binop);
          }

          for (auto *binop : bare_ops) {
            int64_t offset = 0;
            traceToBase(binop, base, offset);
            int64_t idx = offset - min_off;
            llvm::IRBuilder<> Builder(binop->getNextNode());
            auto *gep = Builder.CreateGEP(i8_ty, frame_alloca,
                llvm::ConstantInt::get(i64_ty, idx), "frame_addr");
            auto *pti = Builder.CreatePtrToInt(gep, i64_ty, "frame_int");
            binop->replaceAllUsesWith(pti);
            binop->eraseFromParent();
            changed = true;
          }
        }
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
