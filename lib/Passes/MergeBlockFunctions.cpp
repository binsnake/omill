#include "omill/Passes/MergeBlockFunctions.h"

#include <llvm/ADT/DenseMap.h>
#include <llvm/ADT/DenseSet.h>
#include <llvm/ADT/PostOrderIterator.h>
#include <llvm/ADT/SmallVector.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/Module.h>
#include <llvm/Transforms/Utils/Cloning.h>
#include <llvm/Transforms/Utils/ValueMapper.h>

#include "omill/Utils/LiftedNames.h"

namespace omill {

namespace {

/// Prefixes used by BlockLifter for block-function names.  `blk_<pc>` is
/// a plain block body; `sub_<pc>` is a direct-call target or top-level
/// function entry emitted by BlockLifter.  Both are identified by the
/// `omill.block_lifter` function attribute so we never confuse a
/// TraceLifter-produced `sub_<pc>` with a BlockLifter one.
static constexpr const char *kBlockPrefix = "blk_";
static constexpr const char *kSubPrefix = "sub_";
static constexpr const char *kBlockLifterAttr = "omill.block_lifter";

/// Check if a function is a block-function (produced by BlockLifter).
bool isBlockFunction(const llvm::Function &F) {
  if (F.isDeclaration() || !F.hasFnAttribute(kBlockLifterAttr))
    return false;
  auto name = F.getName();
  return name.starts_with(kBlockPrefix) || name.starts_with(kSubPrefix);
}

/// Extract the block address from a block-function name like
/// "blk_140001000" or "sub_140001000".
std::optional<uint64_t> parseBlockAddr(llvm::StringRef name) {
  llvm::StringRef rest;
  if (name.starts_with(kBlockPrefix))
    rest = name.drop_front(4);
  else if (name.starts_with(kSubPrefix))
    rest = name.drop_front(4);
  else
    return std::nullopt;
  uint64_t addr;
  if (rest.getAsInteger(16, addr))
    return std::nullopt;
  return addr;
}

/// Find a musttail call in a basic block's terminator sequence.
/// Pattern: %r = musttail call ... @blk_xxx(...); ret %r
llvm::CallInst *findMusttailCall(llvm::BasicBlock &BB) {
  auto *term = BB.getTerminator();
  if (!term)
    return nullptr;
  auto *ret = llvm::dyn_cast<llvm::ReturnInst>(term);
  if (!ret)
    return nullptr;

  // The ret should return the result of the musttail call.
  auto *ret_val = ret->getReturnValue();
  if (!ret_val)
    return nullptr;
  auto *call = llvm::dyn_cast<llvm::CallInst>(ret_val);
  if (!call || call->getTailCallKind() != llvm::CallInst::TCK_MustTail)
    return nullptr;
  return call;
}

/// Collect all block-functions called (transitively) from an entry block.
/// Returns a set of block addresses reachable from the entry.
void collectReachableBlocks(
    llvm::Function *entry,
    const llvm::DenseMap<llvm::Function *, uint64_t> &fn_to_addr,
    const llvm::DenseMap<uint64_t, llvm::Function *> &addr_to_fn,
    llvm::DenseSet<uint64_t> &reachable) {

  llvm::SmallVector<llvm::Function *, 16> worklist;
  worklist.push_back(entry);

  while (!worklist.empty()) {
    auto *fn = worklist.pop_back_val();
    auto it = fn_to_addr.find(fn);
    if (it == fn_to_addr.end())
      continue;
    uint64_t addr = it->second;
    if (!reachable.insert(addr).second)
      continue;

    // Scan all basic blocks for musttail calls to other block-functions.
    for (auto &BB : *fn) {
      auto *call = findMusttailCall(BB);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee || !isBlockFunction(*callee))
        continue;
      auto callee_it = fn_to_addr.find(callee);
      if (callee_it != fn_to_addr.end())
        worklist.push_back(callee);
    }
  }
}

llvm::SmallVector<uint64_t, 16> getMergeOrder(
    uint64_t entry_addr, const llvm::DenseSet<uint64_t> &group_addrs) {
  llvm::SmallVector<uint64_t, 16> ordered_addrs;
  ordered_addrs.reserve(group_addrs.size());
  if (group_addrs.contains(entry_addr))
    ordered_addrs.push_back(entry_addr);
  for (uint64_t addr : group_addrs) {
    if (addr != entry_addr)
      ordered_addrs.push_back(addr);
  }
  if (ordered_addrs.size() > 1)
    llvm::sort(ordered_addrs.begin() + 1, ordered_addrs.end());
  return ordered_addrs;
}


/// Build a merged function from a group of block-functions.
/// The entry block-function becomes the merged function; all other
/// block-functions are inlined.
llvm::Function *mergeBlockGroup(
    uint64_t entry_addr,
    const llvm::DenseSet<uint64_t> &group_addrs,
    const llvm::DenseMap<uint64_t, llvm::Function *> &addr_to_fn,
    llvm::Module &M) {

  auto entry_it = addr_to_fn.find(entry_addr);
  if (entry_it == addr_to_fn.end())
    return nullptr;

  llvm::Function *entry_fn = entry_it->second;

  // If this is a single block with no internal musttail calls to other
  // blocks in the group (including itself), there's nothing to merge.
  if (group_addrs.size() <= 1) {
    // Check if the single block calls itself (self-loop).
    bool has_self_call = false;
    for (auto &BB : *entry_fn) {
      auto *call = findMusttailCall(BB);
      if (call && call->getCalledFunction() == entry_fn) {
        has_self_call = true;
        break;
      }
    }
    if (!has_self_call && !entry_fn->hasFnAttribute("omill.output_root"))
      return entry_fn;
  }

  // Create the merged function with a trace-like name.
  auto &Ctx = M.getContext();
  auto *fn_type = entry_fn->getFunctionType();

  char name_buf[64];
  snprintf(name_buf, sizeof(name_buf), "sub_%llx",
           (unsigned long long)entry_addr);

  // BlockLifter may already have produced `sub_<entry_addr>` for this
  // function entry (direct-call target or top-level lift target).  In
  // that case, temporarily rename the pre-existing function so the new
  // merged function can claim the canonical name, then RAUW external
  // users over to the merged function once the clone is complete.
  llvm::Function *pre_existing = M.getFunction(name_buf);
  if (pre_existing && pre_existing != entry_fn)
    pre_existing = nullptr;  // unrelated collision — leave it alone
  if (pre_existing)
    pre_existing->setName(llvm::Twine(name_buf) + ".premerge");

  auto *merged_fn =
      llvm::Function::Create(fn_type, llvm::GlobalValue::ExternalLinkage,
                             name_buf, &M);
  merged_fn->setCallingConv(entry_fn->getCallingConv());
  if (entry_fn->hasFnAttribute("omill.output_root"))
    merged_fn->addFnAttr("omill.output_root");
  if (entry_fn->hasFnAttribute("omill.closed_root_slice"))
    merged_fn->addFnAttr("omill.closed_root_slice", "1");
  if (entry_fn->hasFnAttribute("omill.closed_root_slice_root"))
    merged_fn->addFnAttr("omill.closed_root_slice_root", "1");

  // Keep the chosen root as the actual function entry block instead of
  // inheriting DenseSet iteration order.
  auto group_order = getMergeOrder(entry_addr, group_addrs);

  // Map: block addr -> BasicBlock in the merged function.
  llvm::DenseMap<uint64_t, llvm::BasicBlock *> block_map;

  // Create one BasicBlock per block-function in the merged function.
  for (uint64_t addr : group_order) {
    char bb_name[64];
    snprintf(bb_name, sizeof(bb_name), "block_%llx",
             (unsigned long long)addr);
    auto *bb = llvm::BasicBlock::Create(Ctx, bb_name, merged_fn);
    block_map[addr] = bb;
  }

  for (uint64_t addr : group_order) {
    auto fn_it = addr_to_fn.find(addr);
    if (fn_it == addr_to_fn.end())
      continue;
    llvm::Function *block_fn = fn_it->second;
    llvm::BasicBlock *target_bb = block_map[addr];

    // The block-function has signature (State*, i64 pc, Memory*) -> Memory*.
    // We need to map its arguments to the merged function's arguments.
    llvm::ValueToValueMapTy VMap;
    for (unsigned i = 0; i < block_fn->arg_size(); ++i) {
      VMap[block_fn->getArg(i)] = merged_fn->getArg(i);
    }

    // Clone the block-function's IR in two phases so internal self-loops and
    // forward references in PHIs are remapped after every local value exists.
    llvm::DenseMap<llvm::BasicBlock *, llvm::BasicBlock *> bb_map;
    bb_map[&block_fn->getEntryBlock()] = target_bb;
    VMap[&block_fn->getEntryBlock()] = target_bb;

    for (auto &BB : *block_fn) {
      if (&BB == &block_fn->getEntryBlock())
        continue;
      char internal_name[128];
      snprintf(internal_name, sizeof(internal_name), "block_%llx.%s",
               (unsigned long long)addr, BB.getName().str().c_str());
      auto *new_bb = llvm::BasicBlock::Create(Ctx, internal_name, merged_fn);
      bb_map[&BB] = new_bb;
      VMap[&BB] = new_bb;
    }

    for (auto &BB : *block_fn) {
      auto *dest_bb = bb_map[&BB];
      llvm::IRBuilder<> builder(dest_bb);
      for (auto &I : BB) {
        if (llvm::isa<llvm::ReturnInst>(&I))
          continue;
        auto *new_inst = I.clone();
        builder.Insert(new_inst);
        VMap[&I] = new_inst;
      }
    }

    for (auto &BB : *block_fn) {
      auto *dest_bb = bb_map[&BB];
      for (auto &I : *dest_bb) {
        llvm::RemapInstruction(
            &I, VMap, llvm::RF_NoModuleLevelChanges);
      }
    }
  }

  // Now replace musttail calls to block-functions within the group
  // with branches to the corresponding BasicBlock.
  llvm::SmallVector<std::pair<llvm::CallInst *, llvm::BasicBlock *>, 16>
      calls_to_replace;

  for (auto &BB : *merged_fn) {
    auto *call = findMusttailCall(BB);
    if (!call)
      continue;
    auto *callee = call->getCalledFunction();
    if (!callee)
      continue;
    auto callee_addr = parseBlockAddr(callee->getName());
    if (!callee_addr)
      continue;
    auto target_it = block_map.find(*callee_addr);
    if (target_it == block_map.end())
      continue;
    calls_to_replace.push_back({call, target_it->second});
  }

  for (auto &[call, target_bb] : calls_to_replace) {
    auto *call_bb = call->getParent();
    auto *ret = call_bb->getTerminator();

    // Remove the ret + musttail call, replace with branch.
    ret->eraseFromParent();
    call->replaceAllUsesWith(llvm::PoisonValue::get(call->getType()));
    call->eraseFromParent();

    // Remove any dead instructions between the branch point and the
    // former terminator position (shouldn't be any, but be safe).
    llvm::IRBuilder<> builder(call_bb);
    builder.CreateBr(target_bb);
  }

  // Handle returns: for blocks that end in a musttail call to a
  // block NOT in the group (or to __omill_dispatch_*), the cloned
  // code doesn't have a terminator. Add ret instructions.
  for (auto &BB : *merged_fn) {
    if (!BB.getTerminator()) {
      // Find the last call instruction (should be the dispatch or
      // external block call) and make it a proper return.
      llvm::Value *last_call_result = nullptr;
      for (auto it = BB.rbegin(); it != BB.rend(); ++it) {
        if (auto *ci = llvm::dyn_cast<llvm::CallInst>(&*it)) {
          last_call_result = ci;
          break;
        }
      }
      llvm::IRBuilder<> builder(&BB);
      if (last_call_result &&
          last_call_result->getType() == fn_type->getReturnType()) {
        builder.CreateRet(last_call_result);
      } else {
        builder.CreateRet(
            llvm::PoisonValue::get(fn_type->getReturnType()));
      }
    }
  }

  // Redirect external users of the pre-existing `sub_<entry_addr>` to
  // the merged function; the now-orphaned `.premerge` stub is left for
  // the outer loop / GlobalDCE to clean up alongside the other group
  // members.
  if (pre_existing) {
    pre_existing->replaceAllUsesWith(merged_fn);
  }

  return merged_fn;
}

}  // namespace

llvm::PreservedAnalyses MergeBlockFunctionsPass::run(
    llvm::Module &M, llvm::ModuleAnalysisManager &MAM) {

  // Index all block-functions.
  llvm::DenseMap<llvm::Function *, uint64_t> fn_to_addr;
  llvm::DenseMap<uint64_t, llvm::Function *> addr_to_fn;

  for (auto &F : M) {
    if (!isBlockFunction(F))
      continue;
    auto addr = parseBlockAddr(F.getName());
    if (!addr)
      continue;
    fn_to_addr[&F] = *addr;
    addr_to_fn[*addr] = &F;
  }

  if (fn_to_addr.empty())
    return llvm::PreservedAnalyses::all();

  // Find entry points: block-functions that are not called by any other
  // block-function's musttail call. These are the trace entry points.
  llvm::DenseSet<uint64_t> called_addrs;
  for (auto &[fn, addr] : fn_to_addr) {
    for (auto &BB : *fn) {
      auto *call = findMusttailCall(BB);
      if (!call)
        continue;
      auto *callee = call->getCalledFunction();
      if (!callee)
        continue;
      auto callee_addr = parseBlockAddr(callee->getName());
      if (callee_addr)
        called_addrs.insert(*callee_addr);
    }
  }

  llvm::SmallVector<uint64_t, 16> entry_addrs;
  llvm::SmallVector<uint64_t, 8> rooted_entry_addrs;
  for (auto &[addr, fn] : addr_to_fn) {
    if (fn->hasFnAttribute("omill.output_root"))
      rooted_entry_addrs.push_back(addr);
    if (!called_addrs.contains(addr))
      entry_addrs.push_back(addr);
  }

  // Explicit output roots take priority in flattened/loop-heavy CFGs where
  // the function entry may be back-edge reachable and therefore look like a
  // non-entry structurally.
  if (!rooted_entry_addrs.empty())
    entry_addrs = std::move(rooted_entry_addrs);

  // If no clear entry points, all blocks call each other (degenerate).
  // Use the lowest address as entry.
  if (entry_addrs.empty()) {
    uint64_t min_addr = UINT64_MAX;
    for (auto &[addr, fn] : addr_to_fn) {
      if (addr < min_addr)
        min_addr = addr;
    }
    entry_addrs.push_back(min_addr);
  }

  llvm::sort(entry_addrs);

  bool changed = false;

  // For each entry point, collect its reachable group and merge.
  llvm::DenseSet<uint64_t> already_merged;
  for (uint64_t entry_addr : entry_addrs) {
    if (already_merged.contains(entry_addr))
      continue;

    llvm::DenseSet<uint64_t> group;
    collectReachableBlocks(addr_to_fn[entry_addr], fn_to_addr, addr_to_fn,
                           group);

    // Mark all group members as merged so we don't process them again
    // as a separate entry.
    for (uint64_t addr : group)
      already_merged.insert(addr);

    auto *merged = mergeBlockGroup(entry_addr, group, addr_to_fn, M);
    if (!merged)
      continue;

    changed = true;

    // Mark original block-functions as internal so GlobalDCE removes them.
    for (uint64_t addr : group) {
      auto it = addr_to_fn.find(addr);
      if (it != addr_to_fn.end()) {
        if (it->second == merged)
          continue;
        it->second->setLinkage(llvm::GlobalValue::InternalLinkage);
        it->second->removeDeadConstantUsers();
      }
    }
  }

  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}

}  // namespace omill
