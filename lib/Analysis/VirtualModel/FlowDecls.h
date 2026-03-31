#pragma once

#include "Analysis/VirtualModel/DetailTypes.h"

namespace omill {
class VMTraceMap;
}

namespace omill::virtual_model::detail {
void canonicalizeVirtualState(VirtualMachineModel &model);
void propagateVirtualStateFacts(llvm::Module &M, VirtualMachineModel &model,
                                const BinaryMemoryMap &binary_memory,
                                CachedModuleHandlerSummaryState *module_cache);
void summarizeVirtualInstructionPointers(llvm::Module &M,
                                         VirtualMachineModel &model,
                                         const BinaryMemoryMap &binary_memory);
void summarizeVirtualRegions(VirtualMachineModel &model,
                             const BinaryMemoryMap &binary_memory);
void summarizeDispatchSuccessors(llvm::Module &M, VirtualMachineModel &model,
                                 const BinaryMemoryMap &binary_memory);
void summarizeCallSites(llvm::Module &M, VirtualMachineModel &model,
                        const BinaryMemoryMap &binary_memory);
void summarizeVirtualExits(llvm::Module &M, VirtualMachineModel &model,
                           const BinaryMemoryMap &binary_memory,
                           const VMTraceMap *trace_map = nullptr);
void summarizeRootSlices(llvm::Module &M, VirtualMachineModel &model,
                         const BinaryMemoryMap &binary_memory);
std::map<unsigned, VirtualValueExpr> rebaseOutgoingStackFacts(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    const std::map<unsigned, VirtualValueExpr> &outgoing_stack);
std::optional<llvm::SmallVector<llvm::BasicBlock *, 4>>
collectLocalizedReplayBlocks(llvm::Function &F,
                             const VirtualHandlerSummary &summary);
std::optional<CallsiteLocalizedOutgoingFacts>
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
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    llvm::CallBase *localizing_call = nullptr,
    const std::map<unsigned, VirtualValueExpr> *caller_stack_facts = nullptr,
    const std::map<unsigned, VirtualValueExpr> *caller_slot_facts = nullptr,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_stack_facts = nullptr,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts =
        nullptr,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts =
        nullptr,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts = nullptr,
    LocalizedReplayCacheState *localized_replay_cache = nullptr);
bool mergeFactIntoMap(std::map<unsigned, VirtualValueExpr> &dst, unsigned id,
                      const VirtualValueExpr &value);
llvm::SmallDenseSet<unsigned, 16> rebaseWrittenStackCellIds(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    llvm::ArrayRef<unsigned> written_stack_cell_ids);
unsigned rebaseSingleStackCellId(
    const VirtualMachineModel &model,
    const std::map<unsigned, VirtualValueExpr> &outgoing_slots,
    unsigned cell_id);

LocalCallSiteState computeLocalFactsBeforeCall(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &base_slot_facts,
    const std::map<unsigned, VirtualValueExpr> &base_stack_facts,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);
VirtualValueExpr summarizeSpecializedCallArg(
    llvm::CallBase &call, unsigned arg_index, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);
std::map<unsigned, VirtualValueExpr> buildSpecializedCallArgumentMap(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    llvm::ArrayRef<unsigned> requested_arg_indices = {});
std::optional<uint64_t> resolveSpecializedExprToConstant(
    const VirtualValueExpr &expr,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack);
ResolvedCallSiteInfo resolveCallSiteInfo(
    llvm::CallBase &call, const llvm::DataLayout &dl,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);
std::optional<CallsiteLocalizedOutgoingFacts>
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
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_stack_facts = nullptr,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts =
        nullptr,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts =
        nullptr,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts = nullptr,
    LocalizedReplayCacheState *localized_replay_cache = nullptr,
    const LocalCallSiteState *precomputed_local_call_state = nullptr,
    llvm::StringRef specialized_arg_cache_key_hint = "");
std::optional<CallsiteLocalizedOutgoingFacts>
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
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    const ResolvedCallSiteInfo &callsite,
    const BinaryMemoryMap &binary_memory, unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);
std::optional<CallsiteLocalizedOutgoingFacts>
computeEntryPreludeCallOutgoingFacts(
    llvm::Module &M, const VirtualMachineModel &model,
    const VirtualHandlerSummary &target_summary,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming,
    const std::map<unsigned, VirtualValueExpr> &caller_incoming_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    uint64_t continuation_pc, const BinaryMemoryMap &binary_memory,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting);
std::optional<VirtualValueExpr> normalizeLocalizedExprForCaller(
    const VirtualValueExpr &expr, const llvm::Function &caller_fn,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);
std::optional<unsigned> lookupMappedCallerSlotId(
    llvm::CallBase &call, const VirtualStateSlotInfo &callee_slot,
    const std::map<SlotKey, unsigned> &slot_ids, const llvm::DataLayout &dl);
std::optional<unsigned> lookupMappedCallerStackCellId(
    llvm::CallBase &call, const VirtualStackCellInfo &callee_cell,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl);
VirtualValueExpr remapCalleeExprToCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl);
std::optional<VirtualValueExpr> normalizeImportedExprForCaller(
    const VirtualValueExpr &expr, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    const std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const std::map<StackCellKey, VirtualValueExpr>
        *caller_structural_outgoing_stack,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map);
std::optional<StackCellKey> remapCalleeStructuralStackKeyToCaller(
    const StackCellKey &key, llvm::CallBase &call,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const llvm::DataLayout &dl);
bool applySingleDirectCalleeEffects(
    llvm::Function &caller_fn, llvm::CallBase &call,
    const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    std::map<StackCellKey, VirtualValueExpr> &caller_structural_outgoing_stack,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const llvm::DataLayout &dl, const BinaryMemoryMap &binary_memory,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    const std::map<StackCellKey, VirtualValueExpr>
        *fallback_caller_structural_stack_facts = nullptr,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_stack_facts =
        nullptr,
    const std::map<unsigned, VirtualValueExpr> *fallback_caller_slot_facts =
        nullptr,
    LocalizedReplayCacheState *localized_replay_cache = nullptr,
    llvm::ArrayRef<unsigned> relevant_caller_slot_ids = {},
    llvm::ArrayRef<unsigned> relevant_caller_stack_cell_ids = {});
void applyDirectCalleeEffectsImpl(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    std::map<StackCellKey, VirtualValueExpr> &caller_structural_outgoing_stack,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    const llvm::DataLayout &dl, const BinaryMemoryMap &binary_memory,
    unsigned depth,
    llvm::SmallPtrSetImpl<const llvm::Function *> &visiting,
    LocalizedReplayCacheState *localized_replay_cache = nullptr,
    llvm::ArrayRef<unsigned> relevant_caller_slot_ids = {},
    llvm::ArrayRef<unsigned> relevant_caller_stack_cell_ids = {});
void applyDirectCalleeEffects(
    llvm::Function &caller_fn, const VirtualMachineModel &model,
    const std::map<std::string, size_t> &handler_index,
    const std::vector<std::map<unsigned, VirtualValueExpr>> &outgoing_maps,
    const std::vector<std::map<unsigned, VirtualValueExpr>>
        &outgoing_stack_maps,
    const std::map<unsigned, VirtualValueExpr> &caller_argument_map,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing,
    std::map<unsigned, VirtualValueExpr> &caller_outgoing_stack,
    const BinaryMemoryMap &binary_memory,
    LocalizedReplayCacheState *localized_replay_cache = nullptr,
    llvm::ArrayRef<unsigned> relevant_caller_slot_ids = {},
    llvm::ArrayRef<unsigned> relevant_caller_stack_cell_ids = {});
bool canRecursivelyLocalizeCallsiteSummary(
    const VirtualHandlerSummary &summary, unsigned depth);
bool isCallerStateArgumentExpr(const VirtualValueExpr &expr);
bool canComputeLocalizedSingleBlockOutgoingFacts(
    const llvm::Function &F, const VirtualHandlerSummary &summary);
void seedCallContinuationStackCell(
    llvm::Module &M, uint64_t continuation_pc,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    std::map<unsigned, VirtualValueExpr> &callee_incoming_stack);
void seedLiftedCallContinuationStackCell(
    llvm::CallBase &call, const VirtualHandlerSummary &callee_summary,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info,
    std::map<unsigned, VirtualValueExpr> &callee_incoming_stack);

std::optional<EntryPreludeCallInfo> detectEntryPreludeDirectCall(
    const BinaryMemoryMap &binary_memory, uint64_t entry_va);
std::optional<uint64_t> inferLiftedCallContinuationPc(llvm::CallBase &call);
const VirtualHandlerSummary *lookupHandlerByEntryVA(
    const VirtualMachineModel &model, uint64_t entry_va);
const VirtualHandlerSummary *findNearbyLiftedHandlerEntry(
    const VirtualMachineModel &model, uint64_t target_pc, TargetArch arch);
std::optional<std::string> resolveBoundaryNameForTarget(
    const VirtualMachineModel &model, const BinaryMemoryMap &binary_memory,
    uint64_t pc);
bool isTargetMapped(const BinaryMemoryMap &binary_memory, uint64_t target_pc);
bool isTargetExecutable(const BinaryMemoryMap &binary_memory, uint64_t target_pc);
const BinaryMemoryMap::ImportEntry *lookupImportTarget(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc);
TargetArch targetArchForModule(llvm::Module &M);
std::optional<bool> isTargetDecodableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc, TargetArch arch);
std::optional<uint64_t> findNearbyExecutableEntry(
    const BinaryMemoryMap &binary_memory, uint64_t target_pc, TargetArch arch);

}  // namespace omill::virtual_model::detail
