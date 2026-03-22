#pragma once

#include "Analysis/VirtualModel/DetailTypes.h"

#include <chrono>

namespace omill::virtual_model::detail {
std::map<const llvm::Module *, CachedModuleHandlerSummaryState> &
virtualModelSummaryCaches();

void vmModelImportDebugLog(llvm::StringRef message);
void vmModelStageDebugLog(llvm::StringRef message);
bool vmModelLocalReplayDebugEnabled();
void vmModelLocalReplayDebugLog(llvm::StringRef message);

uint64_t elapsedMilliseconds(std::chrono::steady_clock::time_point begin,
                             std::chrono::steady_clock::time_point end);

std::optional<uint64_t> extractHexAttr(const llvm::Function &F,
                                       llvm::StringRef attr_name);
void collectExprReferencedStateSlots(
    const VirtualValueExpr &expr,
    std::vector<VirtualStateSlotSummary> &slots);
SlotKey slotKeyForSummary(const VirtualStateSlotSummary &slot);
StackCellKey stackCellKeyForSummary(const VirtualStackCellSummary &cell);
std::optional<unsigned> findEquivalentArgumentStackCellId(
    int64_t base_offset, unsigned base_width, bool base_from_argument,
    bool base_from_alloca, int64_t cell_offset, unsigned width,
    const std::map<StackCellKey, unsigned> &stack_cell_ids);
std::optional<unsigned> parseArgumentBaseName(llvm::StringRef base_name);
std::optional<unsigned> remillMemoryBitWidth(llvm::StringRef name);
bool isRemillReadMemoryIntrinsic(const llvm::Function &F);
bool isRemillWriteMemoryIntrinsic(const llvm::Function &F);
bool isRemillTerminalControlIntrinsic(const llvm::Function &F);
unsigned getValueBitWidth(llvm::Value *V, const llvm::DataLayout &dl);
std::optional<VirtualStateSlotSummary> extractStateSlotSummary(
    llvm::Value *ptr, unsigned width, const llvm::DataLayout &dl);
std::optional<unsigned> nativeStackPointerOffsetForValue(llvm::Value *V);
std::optional<VirtualStackCellSummary> extractStackCellSummaryFromExpr(
    const VirtualValueExpr &expr, unsigned width,
    std::optional<unsigned> native_sp_offset = std::nullopt);
std::optional<unsigned> lookupNativeStackPointerOffset(llvm::Module &M);
uint64_t bitMask(unsigned bits);
uint64_t signExtendBits(uint64_t value, unsigned from_bits);
VirtualValueExpr constantExpr(uint64_t value, unsigned bits);
VirtualValueExpr argumentExpr(unsigned index, unsigned bits = 64);
VirtualValueExpr castExpr(const VirtualValueExpr &expr,
                          llvm::Instruction::CastOps opcode,
                          unsigned target_bits);
VirtualExprKind classifyExprKind(unsigned opcode);
VirtualExprKind classifyICmpPredicate(llvm::CmpInst::Predicate pred);
VirtualValueExpr summarizeValueExpr(llvm::Value *V,
                                    const llvm::DataLayout &dl);
VirtualValueExpr unknownExpr(unsigned bits = 0);
std::optional<VirtualValueExpr> readBinaryConstantExpr(
    const BinaryMemoryMap &binary_memory, uint64_t addr, unsigned width_bits);
std::optional<VirtualValueExpr> mergeIncomingExpr(
    const VirtualValueExpr &existing, const VirtualValueExpr &incoming);
std::optional<uint64_t> evaluateVirtualExpr(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    const BinaryMemoryMap *binary_memory = nullptr);
std::map<unsigned, VirtualValueExpr> factMapFor(
    llvm::ArrayRef<VirtualSlotFact> facts);
std::map<unsigned, VirtualValueExpr> stackFactMapFor(
    llvm::ArrayRef<VirtualStackFact> facts);
std::map<unsigned, VirtualValueExpr> argumentFactMapFor(
    llvm::ArrayRef<VirtualArgumentFact> facts);
std::vector<VirtualSlotFact> computeOutgoingFacts(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack = {},
    const std::map<unsigned, VirtualValueExpr> &incoming_args = {});
std::vector<VirtualStackFact> computeOutgoingStackFacts(
    const VirtualHandlerSummary &summary,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> &incoming_stack = {},
    const std::map<unsigned, VirtualValueExpr> &incoming_args = {});
std::vector<VirtualSlotFact> slotFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts);
std::vector<VirtualStackFact> stackFactsForMap(
    const std::map<unsigned, VirtualValueExpr> &facts);
std::map<SlotKey, unsigned> buildSlotIdMap(const VirtualMachineModel &model);
std::map<unsigned, const VirtualStateSlotInfo *> buildSlotInfoMap(
    const VirtualMachineModel &model);
std::optional<unsigned> lookupSlotIdForSummary(
    const VirtualStateSlotSummary &summary,
    const std::map<SlotKey, unsigned> &slot_ids);
std::map<StackCellKey, unsigned> buildStackCellIdMap(
    const VirtualMachineModel &model);
std::map<unsigned, const VirtualStackCellInfo *> buildStackCellInfoMap(
    const VirtualMachineModel &model);
std::optional<unsigned> lookupStackCellIdForSummary(
    const VirtualStackCellSummary &summary,
    const std::map<StackCellKey, unsigned> &stack_cell_ids);
std::optional<VirtualStateSlotSummary> extractStateSlotSummaryFromExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info);
void canonicalizeMemoryReadsToStackCells(
    VirtualValueExpr &expr,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<SlotKey, unsigned> &slot_ids);
std::vector<CachedStableArgumentFactEntry> captureStableArgumentFacts(
    const std::map<unsigned, VirtualValueExpr> &facts);
std::vector<CachedStableSlotFactEntry> captureStableSlotFacts(
    const std::map<unsigned, VirtualValueExpr> &facts,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info);
std::vector<CachedStableStackFactEntry> captureStableStackFacts(
    const std::map<unsigned, VirtualValueExpr> &facts,
    const std::map<unsigned, const VirtualStackCellInfo *> &stack_cell_info);
std::map<unsigned, VirtualValueExpr> restoreStableArgumentFactMap(
    const std::vector<CachedStableArgumentFactEntry> &facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids);
std::map<unsigned, VirtualValueExpr> restoreStableSlotFactMap(
    const std::vector<CachedStableSlotFactEntry> &facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids);
std::map<unsigned, VirtualValueExpr> restoreStableStackFactMap(
    const std::vector<CachedStableStackFactEntry> &facts,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids);
llvm::DenseSet<unsigned> buildBooleanFlagSlotIds(
    llvm::Module &M, const VirtualMachineModel &model);
std::set<BooleanSlotExprKey> buildBooleanFlagExprKeys(
    llvm::Module &M, const VirtualMachineModel &model);
void annotateExprSlots(VirtualValueExpr &expr,
                       const std::map<SlotKey, unsigned> &slot_ids);
void annotateExprStackCells(
    VirtualValueExpr &expr,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    const std::map<SlotKey, unsigned> &slot_ids);
bool exprEquals(const VirtualValueExpr &lhs, const VirtualValueExpr &rhs);
bool isUnknownLikeExpr(const VirtualValueExpr &expr);
bool containsArgumentExpr(const VirtualValueExpr &expr);
bool isBoundedLocalizedTransferExpr(const VirtualValueExpr &expr,
                                    unsigned depth = 0);
bool containsStateSlotExpr(const VirtualValueExpr &expr);
bool containsStackCellExpr(const VirtualValueExpr &expr);
bool containsMemoryReadExpr(const VirtualValueExpr &expr);
unsigned exprByteWidth(const VirtualValueExpr &expr, unsigned fallback = 8);
unsigned countSymbolicRefs(const VirtualValueExpr &expr);
bool isBoundedStateProvenanceExpr(const VirtualValueExpr &expr,
                                  unsigned depth = 0);
bool isBoundedArgumentFactExpr(const VirtualValueExpr &expr,
                               unsigned depth = 0);
VirtualValueExpr castExprToBitWidth(const VirtualValueExpr &expr,
                                    unsigned target_bits);
std::optional<VirtualValueExpr> simplifyMaskedLowBitReconstruction(
    const VirtualValueExpr &preserved_high_bits,
    const VirtualValueExpr &inserted_low_bits, unsigned result_bits);
std::optional<VirtualValueExpr> mergeLowBitsIntoWiderStateExpr(
    const VirtualValueExpr &existing_wide, unsigned wide_bits,
    const VirtualValueExpr &written_value, unsigned written_bits,
    std::optional<unsigned> self_slot_id = std::nullopt);
void propagateAliasedStateSlotWrite(
    std::map<unsigned, VirtualValueExpr> &slot_facts, unsigned written_slot_id,
    const VirtualValueExpr &written_value,
    const std::map<unsigned, const VirtualStateSlotInfo *> &slot_info);
bool isIdentitySlotExpr(const VirtualValueExpr &expr, unsigned slot_id);
bool isIdentityStackCellExpr(const VirtualValueExpr &expr, unsigned cell_id);
bool isSimpleRemappableFactExpr(const VirtualValueExpr &expr,
                                unsigned depth = 0);
bool containsCallerLocalAllocaStateExpr(const VirtualValueExpr &expr);
bool isGloballyMergeableStateFactExpr(const VirtualValueExpr &expr,
                                      bool allow_arguments);
bool collectEvaluatedTargetChoices(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    const llvm::DenseSet<unsigned> *boolean_slot_ids,
    const std::set<BooleanSlotExprKey> *boolean_slot_expr_keys,
    llvm::SmallVectorImpl<uint64_t> &pcs,
    const BinaryMemoryMap *binary_memory = nullptr);
bool collectEvaluatedValueChoices(
    const VirtualValueExpr &expr, const std::vector<VirtualSlotFact> &facts,
    const std::vector<VirtualStackFact> &stack_facts,
    llvm::SmallVectorImpl<uint64_t> &values,
    const BinaryMemoryMap *binary_memory = nullptr);
VirtualValueExpr stateSlotExpr(const VirtualStateSlotSummary &slot);
VirtualValueExpr stackCellExpr(const VirtualStackCellSummary &cell);
VirtualValueExpr specializeExpr(
    const VirtualValueExpr &expr,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> *incoming_stack = nullptr,
    const std::map<unsigned, VirtualValueExpr> *incoming_args = nullptr);
VirtualValueExpr specializeExprToFixpoint(
    VirtualValueExpr expr,
    const std::map<unsigned, VirtualValueExpr> &incoming,
    const std::map<unsigned, VirtualValueExpr> *incoming_stack,
    const std::map<unsigned, VirtualValueExpr> *incoming_args,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    unsigned max_rounds = 4);
void specializeFactStateToFixpoint(
    std::map<unsigned, VirtualValueExpr> &slot_facts,
    std::map<unsigned, VirtualValueExpr> &stack_facts,
    const std::map<unsigned, VirtualValueExpr> *incoming_args,
    const std::map<SlotKey, unsigned> &slot_ids,
    const std::map<StackCellKey, unsigned> &stack_cell_ids,
    unsigned max_rounds = 4);

VirtualBoundaryKind classifyBoundaryKind(const llvm::Function &F);
bool isBoundaryFunction(const llvm::Function &F);
bool isCallSiteHelper(const llvm::Function &F);
bool isVirtualModelInitialSeedFunction(const llvm::Function &F);
bool isVirtualModelCodeBearingFunction(const llvm::Function &F);

llvm::stable_hash summaryRelevantFunctionFingerprint(const llvm::Function &F);
VirtualHandlerSummary summarizeFunction(llvm::Function &F);
llvm::SmallVector<std::string, 8> collectDirectCalleesForFunction(
    const llvm::Function &F);

}  // namespace omill::virtual_model::detail
