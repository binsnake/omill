#include "omill/Passes/MergeDecomposedStatePHIs.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringMap.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/Support/Casting.h>

using namespace llvm;

namespace omill {

namespace {

struct FieldPiece {
  PHINode *phi;
  unsigned bit_width;
  unsigned bit_offset;
};

/// Parse a PHI name like "state_2280.sroa.0.sroa.761.0" and extract
/// the State field prefix ("state_2280").
/// Returns the prefix, or "" on failure.
static StringRef parseStatePHIPrefix(PHINode *phi) {
  auto name = phi->getName();
  if (!name.starts_with("state_"))
    return "";
  auto dot = name.find('.');
  if (dot == StringRef::npos)
    return "";
  return name.substr(0, dot);
}

/// Find the bit offset of a sub-field PHI by looking at its users.
/// If a user is `zext ... to i64` → `shl ..., <const>`, the const
/// is the bit offset.  If just `zext ... to i64` with no shift, offset=0.
static int findBitOffset(PHINode *phi) {
  for (auto *U : phi->users()) {
    auto *zext = dyn_cast<ZExtInst>(U);
    if (!zext)
      continue;
    for (auto *ZU : zext->users()) {
      if (auto *shl = dyn_cast<BinaryOperator>(ZU)) {
        if (shl->getOpcode() == Instruction::Shl) {
          if (auto *CI = dyn_cast<ConstantInt>(shl->getOperand(1)))
            return static_cast<int>(CI->getZExtValue());
        }
      }
      if (auto *or_inst = dyn_cast<BinaryOperator>(ZU)) {
        if (or_inst->getOpcode() == Instruction::Or)
          return 0;
      }
    }
    if (zext->getType()->isIntegerTy(64))
      return 0;
  }
  if (phi->getType()->isIntegerTy(64)) {
    for (auto *U : phi->users()) {
      if (auto *and_inst = dyn_cast<BinaryOperator>(U)) {
        if (and_inst->getOpcode() == Instruction::And) {
          if (auto *CI = dyn_cast<ConstantInt>(and_inst->getOperand(1))) {
            if (CI->getZExtValue() == 0xFFFFFFFFFFFFFF00ULL)
              return 0;
          }
        }
      }
    }
  }
  return -1;
}

}  // namespace

PreservedAnalyses MergeDecomposedStatePHIsPass::run(Function &F,
                                                    FunctionAnalysisManager &) {
  bool changed = false;

  for (auto &BB : F) {
    // Collect PHIs by State field prefix.
    StringMap<SmallVector<PHINode *, 4>> groups;
    for (auto &I : BB) {
      auto *phi = dyn_cast<PHINode>(&I);
      if (!phi)
        break;  // PHIs are always at block start
      StringRef prefix = parseStatePHIPrefix(phi);
      if (prefix.empty())
        continue;
      groups[prefix].push_back(phi);
    }

    for (auto &[prefix, phis] : groups) {
      if (phis.size() < 2)
        continue;

      unsigned total_bits = 0;
      for (auto *phi : phis)
        total_bits += phi->getType()->getScalarSizeInBits();
      if (total_bits != 64)
        continue;

      SmallVector<FieldPiece, 4> pieces;
      bool all_resolved = true;
      for (auto *phi : phis) {
        int offset = findBitOffset(phi);
        if (offset < 0) {
          all_resolved = false;
          break;
        }
        pieces.push_back(
            {phi, phi->getType()->getScalarSizeInBits(),
             static_cast<unsigned>(offset)});
      }
      if (!all_resolved)
        continue;

      llvm::sort(pieces,
                 [](const auto &a, const auto &b) {
                   return a.bit_offset < b.bit_offset;
                 });

      // Verify contiguous, non-overlapping.
      unsigned expected = 0;
      bool valid = true;
      for (auto &p : pieces) {
        if (p.bit_offset != expected) {
          valid = false;
          break;
        }
        expected += p.bit_width;
      }
      if (!valid || expected != 64)
        continue;

      // Build the merged i64 PHI.
      auto *merged = PHINode::Create(Type::getInt64Ty(F.getContext()),
                                     phis[0]->getNumIncomingValues(),
                                     prefix.str(), BB.getFirstNonPHIIt());

      // For each incoming edge, assemble the i64 value from pieces.
      for (unsigned i = 0; i < phis[0]->getNumIncomingValues(); ++i) {
        auto *incoming_bb = phis[0]->getIncomingBlock(i);
        auto *term = incoming_bb->getTerminator();
        IRBuilder<> Builder(term);

        Value *assembled = nullptr;
        for (auto &p : pieces) {
          auto *val = p.phi->getIncomingValueForBlock(incoming_bb);
          auto *ext = Builder.CreateZExt(val, Type::getInt64Ty(F.getContext()));
          if (p.bit_offset > 0)
            ext = Builder.CreateShl(ext, p.bit_offset);
          assembled = assembled ? Builder.CreateOr(assembled, ext) : ext;
        }
        merged->addIncoming(assembled, incoming_bb);
      }

      // Replace uses of sub-field PHIs with extracts from merged.
      IRBuilder<> ExtractBuilder(&*BB.getFirstNonPHIIt());
      for (auto &p : pieces) {
        Value *extracted;
        if (p.bit_offset == 0 && p.bit_width == 64) {
          extracted = merged;
        } else {
          Value *shifted = merged;
          if (p.bit_offset > 0)
            shifted = ExtractBuilder.CreateLShr(merged, p.bit_offset);
          extracted = ExtractBuilder.CreateTrunc(shifted, p.phi->getType());
        }
        p.phi->replaceAllUsesWith(extracted);
        changed = true;
      }

      for (auto it = phis.rbegin(); it != phis.rend(); ++it)
        (*it)->eraseFromParent();
    }
  }

  return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}

}  // namespace omill
