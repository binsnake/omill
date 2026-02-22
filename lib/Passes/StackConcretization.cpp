#include "omill/Passes/StackConcretization.h"

#include <llvm/ADT/DenseMap.h>
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

/// Maximum depth for arithmetic chain tracing.
static constexpr unsigned kMaxTraceDepth = 12;

/// Resolve the byte offset of a GEP chain from the State pointer (arg0).
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

/// Trace an integer value back to base_val + constant_offset.
/// Handles add, sub, and alignment masking (and with negative power of 2).
bool traceToBase(llvm::Value *addr, llvm::Value *base_val, int64_t &offset,
                 unsigned depth = 0) {
  if (depth > kMaxTraceDepth)
    return false;

  if (addr == base_val) {
    offset = 0;
    return true;
  }

  // PHI bases: also accept reaching any non-self incoming value.
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
      // add(X, K) or add(K, X)
      for (unsigned i = 0; i < 2; ++i) {
        if (auto *CI = llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(i))) {
          int64_t sub_off = 0;
          if (traceToBase(binop->getOperand(1 - i), base_val, sub_off,
                          depth + 1)) {
            offset = sub_off + CI->getSExtValue();
            return true;
          }
        }
      }
    }

    if (opcode == llvm::Instruction::Sub) {
      // sub(X, K)
      if (auto *CI =
              llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
        int64_t sub_off = 0;
        if (traceToBase(binop->getOperand(0), base_val, sub_off, depth + 1)) {
          offset = sub_off - CI->getSExtValue();
          return true;
        }
      }
    }

    if (opcode == llvm::Instruction::And) {
      // and(X, -16) — alignment masking.  Treat as identity for base tracing
      // since the offset is rounded down.  We record offset 0 for the mask
      // result; the inttoptr users of the masked value still have their own
      // constant offsets traced normally.
      if (auto *CI =
              llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
        int64_t mask = CI->getSExtValue();
        // Negative power of 2 (e.g., -16, -32, -4096).
        uint64_t umask = static_cast<uint64_t>(mask);
        uint64_t neg = -umask;
        if (mask < 0 && (neg & (neg - 1)) == 0) {
          int64_t sub_off = 0;
          if (traceToBase(binop->getOperand(0), base_val, sub_off,
                          depth + 1)) {
            // The and rounds down.  For concrete offset tracking, treat as
            // the same offset (the alignment only subtracts 0..alignment-1).
            offset = sub_off;
            return true;
          }
        }
      }
    }

    if (opcode == llvm::Instruction::Or) {
      // or(X, K) where K is small — sometimes used instead of add when
      // the base is known to be aligned.  E.g., or(and(rsp,-16), 8).
      if (auto *CI =
              llvm::dyn_cast<llvm::ConstantInt>(binop->getOperand(1))) {
        int64_t orval = CI->getSExtValue();
        if (orval >= 0 && orval < 4096) {
          int64_t sub_off = 0;
          if (traceToBase(binop->getOperand(0), base_val, sub_off,
                          depth + 1)) {
            // Treat or as add for offset purposes.
            offset = sub_off + orval;
            return true;
          }
        }
      }
    }
  }

  return false;
}

/// Check if a value has been derived from base_val through arithmetic,
/// phi nodes, and casts.  Used to detect inttoptr instructions that
/// are related to a stack base even through complex chains.
bool isDerivedFrom(llvm::Value *V, llvm::Value *base_val,
                   llvm::DenseSet<llvm::Value *> &visited,
                   unsigned depth = 0) {
  if (depth > 16)
    return false;
  if (V == base_val)
    return true;

  if (auto *base_phi = llvm::dyn_cast<llvm::PHINode>(base_val)) {
    for (unsigned i = 0; i < base_phi->getNumIncomingValues(); ++i) {
      auto *inc = base_phi->getIncomingValue(i);
      if (inc != base_phi && V == inc)
        return true;
    }
  }

  if (!visited.insert(V).second)
    return false;

  if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(V)) {
    auto opcode = binop->getOpcode();
    if (opcode == llvm::Instruction::Add ||
        opcode == llvm::Instruction::Sub ||
        opcode == llvm::Instruction::And ||
        opcode == llvm::Instruction::Or ||
        opcode == llvm::Instruction::Xor) {
      for (unsigned i = 0; i < 2; ++i) {
        if (isDerivedFrom(binop->getOperand(i), base_val, visited, depth + 1))
          return true;
      }
    }
  }

  if (auto *phi = llvm::dyn_cast<llvm::PHINode>(V)) {
    for (unsigned i = 0; i < phi->getNumIncomingValues(); ++i) {
      if (isDerivedFrom(phi->getIncomingValue(i), base_val, visited,
                        depth + 1))
        return true;
    }
  }

  if (auto *cast = llvm::dyn_cast<llvm::CastInst>(V)) {
    return isDerivedFrom(cast->getOperand(0), base_val, visited, depth + 1);
  }

  return false;
}

/// Check if a value eventually reaches an inttoptr through its users.
bool hasEventualIntToPtrUser(llvm::Value *V,
                             llvm::DenseSet<llvm::Value *> &visited) {
  if (!visited.insert(V).second)
    return false;
  for (auto *user : V->users()) {
    if (llvm::isa<llvm::IntToPtrInst>(user))
      return true;
    if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
      if (hasEventualIntToPtrUser(binop, visited))
        return true;
    }
    if (auto *phi = llvm::dyn_cast<llvm::PHINode>(user)) {
      if (hasEventualIntToPtrUser(phi, visited))
        return true;
    }
  }
  return false;
}

/// Find stack base values: loads from State that eventually reach inttoptr.
/// Unlike RecoverStackFrame, this does NOT require negative offsets — it
/// detects ANY State field load that reaches inttoptr through constant
/// arithmetic chains.
llvm::SmallVector<llvm::Value *, 4> findStackBases(llvm::Function &F) {
  llvm::SmallVector<llvm::Value *, 4> result;

  if (F.arg_empty())
    return result;

  llvm::Value *state_ptr = F.getArg(0);
  auto &DL = F.getDataLayout();

  // Collect State field loads that reach inttoptr.
  llvm::DenseSet<int64_t> stack_field_offsets;
  llvm::DenseMap<int64_t, llvm::SmallVector<llvm::Value *, 2>> effective_bases;

  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64))
        continue;

      int64_t state_off =
          resolveStateGEPOffset(LI->getPointerOperand(), state_ptr, DL);
      if (state_off < 0)
        continue;

      // Only consider RSP (offset 48) and RBP (offset 56) as stack bases.
      // Other registers could be stack-derived but are too risky to assume.
      if (state_off != 48 && state_off != 56)
        continue;

      // Check if this load has ANY user chain that reaches inttoptr.
      // This is the key difference from RecoverStackFrame: we don't
      // require negative offsets.  We also check deeper chains (e.g.,
      // load → sub → and → inttoptr for alignment masking).
      for (auto *user : LI->users()) {
        // Direct inttoptr user.
        if (llvm::isa<llvm::IntToPtrInst>(user)) {
          stack_field_offsets.insert(state_off);
          effective_bases[state_off].push_back(LI);
          break;
        }

        // Check through binary operators, phi nodes, etc.
        llvm::DenseSet<llvm::Value *> visited;
        bool found = false;
        if (auto *binop = llvm::dyn_cast<llvm::BinaryOperator>(user)) {
          found = hasEventualIntToPtrUser(binop, visited);
        } else if (auto *phi = llvm::dyn_cast<llvm::PHINode>(user)) {
          found = hasEventualIntToPtrUser(phi, visited);
        }

        if (found) {
          stack_field_offsets.insert(state_off);

          // Check if the user chain goes through a phi — prefer phi bases.
          bool added_phi = false;
          if (auto *phi = llvm::dyn_cast<llvm::PHINode>(user)) {
            effective_bases[state_off].push_back(phi);
            added_phi = true;
          } else if (auto *binop_u =
                         llvm::dyn_cast<llvm::BinaryOperator>(user)) {
            for (auto *bu : binop_u->users()) {
              if (auto *phi = llvm::dyn_cast<llvm::PHINode>(bu)) {
                llvm::DenseSet<llvm::Value *> vis2;
                if (hasEventualIntToPtrUser(phi, vis2)) {
                  effective_bases[state_off].push_back(phi);
                  added_phi = true;
                  break;
                }
              }
            }
          }
          if (!added_phi) {
            effective_bases[state_off].push_back(LI);
          }
          break;
        }
      }
    }
  }

  if (stack_field_offsets.empty())
    return result;

  // Deduplicate: prefer phi bases over load bases per field.
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
      if (has_phi && !llvm::isa<llvm::PHINode>(base))
        continue;
      if (seen.insert(base).second)
        result.push_back(base);
    }
  }

  // Also collect remaining loads for non-phi fields.
  for (auto &BB : F) {
    for (auto &I : BB) {
      auto *LI = llvm::dyn_cast<llvm::LoadInst>(&I);
      if (!LI || !LI->getType()->isIntegerTy(64))
        continue;

      int64_t state_off =
          resolveStateGEPOffset(LI->getPointerOperand(), state_ptr, DL);
      if (state_off < 0 || !stack_field_offsets.count(state_off))
        continue;
      if (phi_fields.count(state_off))
        continue;

      if (seen.insert(LI).second) {
        // Check it has remaining inttoptr users (not already handled).
        llvm::DenseSet<llvm::Value *> visited;
        if (hasEventualIntToPtrUser(LI, visited))
          result.push_back(LI);
      }
    }
  }

  return result;
}

/// A contiguous region of the stack frame.
struct FrameRegion {
  int64_t min_offset;
  int64_t max_offset;
};

/// Group sorted offsets into contiguous regions with a gap tolerance.
llvm::SmallVector<FrameRegion, 4>
clusterOffsets(llvm::SmallVector<int64_t, 16> &offsets, int64_t gap = 16) {
  llvm::SmallVector<FrameRegion, 4> regions;
  if (offsets.empty())
    return regions;

  llvm::sort(offsets);
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

}  // namespace

llvm::PreservedAnalyses StackConcretizationPass::run(
    llvm::Function &F, llvm::FunctionAnalysisManager &AM) {
  if (F.isDeclaration() || F.empty() || F.arg_size() == 0)
    return llvm::PreservedAnalyses::all();

  auto base_values = findStackBases(F);
  if (base_values.empty())
    return llvm::PreservedAnalyses::all();

  llvm::IRBuilder<> EntryBuilder(&F.getEntryBlock().front());
  auto *i8_ty = EntryBuilder.getInt8Ty();
  auto *i64_ty = EntryBuilder.getInt64Ty();
  bool changed = false;

  for (auto *base : base_values) {
    // Collect all constant-offset inttoptr uses.
    llvm::SmallVector<int64_t, 16> offsets;
    llvm::SmallVector<llvm::IntToPtrInst *, 16> all_itp;

    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&I);
        if (!ITP)
          continue;
        int64_t off = 0;
        if (traceToBase(ITP->getOperand(0), base, off)) {
          offsets.push_back(off);
          all_itp.push_back(ITP);
        }
      }
    }

    if (offsets.empty())
      continue;

    // Check for dynamic (non-constant-offset) inttoptr uses.
    // If present, we skip this base to avoid unsound replacement.
    bool has_dynamic = false;
    for (auto &BB : F) {
      for (auto &I : BB) {
        auto *ITP = llvm::dyn_cast<llvm::IntToPtrInst>(&I);
        if (!ITP)
          continue;
        llvm::DenseSet<llvm::Value *> visited;
        if (isDerivedFrom(ITP->getOperand(0), base, visited)) {
          int64_t off = 0;
          if (!traceToBase(ITP->getOperand(0), base, off)) {
            has_dynamic = true;
            break;
          }
        }
      }
      if (has_dynamic)
        break;
    }

    // With dynamic uses, only process constant-offset inttoptr and leave
    // dynamic ones untouched.
    auto regions = clusterOffsets(offsets, 16);

    for (auto &region : regions) {
      int64_t min_off = region.min_offset;
      int64_t max_off = region.max_offset;
      int64_t frame_size = max_off - min_off + 8;
      if (frame_size <= 0)
        frame_size = 8;
      // Sanity cap: don't create absurdly large allocas.
      if (frame_size > 1 << 20)
        continue;

      auto *frame_ty = llvm::ArrayType::get(i8_ty, frame_size);
      auto *frame_alloca =
          EntryBuilder.CreateAlloca(frame_ty, nullptr, "concrete_stack");

      // Attach metadata recording the RSP base offset so downstream passes
      // (e.g. CallingConventionAnalysis) can reconstruct original offsets.
      auto &Ctx = F.getContext();
      auto *md_offset = llvm::ConstantAsMetadata::get(
          llvm::ConstantInt::get(i64_ty, min_off));
      frame_alloca->setMetadata(
          "omill.stack.base_offset",
          llvm::MDNode::get(Ctx, {md_offset}));

      for (auto *itp : all_itp) {
        int64_t const_off = 0;
        if (!traceToBase(itp->getOperand(0), base, const_off))
          continue;
        if (const_off < min_off || const_off > max_off)
          continue;

        llvm::IRBuilder<> Builder(itp);
        auto *alloca_idx =
            llvm::ConstantInt::get(i64_ty, const_off - min_off);
        auto *gep = Builder.CreateGEP(i8_ty, frame_alloca, alloca_idx,
                                      "stack_ptr");
        itp->replaceAllUsesWith(gep);
        itp->eraseFromParent();
        changed = true;
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
