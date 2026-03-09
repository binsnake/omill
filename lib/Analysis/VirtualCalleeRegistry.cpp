#include "omill/Analysis/VirtualCalleeRegistry.h"

#include <llvm/ADT/SmallVector.h>
#include <llvm/ADT/StringExtras.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Metadata.h>
#include <llvm/IR/Module.h>

#include "omill/Analysis/VMTraceMap.h"

namespace omill {

llvm::AnalysisKey VirtualCalleeRegistryAnalysis::Key;

namespace {

constexpr llvm::StringLiteral kRegistryName = "omill.vm_virtual_callees";

std::optional<uint64_t> parseHexString(llvm::StringRef text) {
  if (text.empty())
    return std::nullopt;
  uint64_t value = 0;
  if (text.getAsInteger(16, value))
    return std::nullopt;
  return value;
}

/// Hash combiner for (handler_va, trace_hash) used as a DenseMap key.
uint64_t traceKeyHash(uint64_t handler_va, uint64_t trace_hash) {
  return trace_hash ^ (handler_va + 0x9E3779B97F4A7C15ull +
                       (trace_hash << 6) + (trace_hash >> 2));
}

}  // namespace

// ---------------------------------------------------------------------------
// Lookups
// ---------------------------------------------------------------------------

std::optional<VirtualCalleeRecord>
VirtualCalleeRegistry::lookup(llvm::StringRef clone_name) const {
  for (const auto &record : records_) {
    if (record.clone_name == clone_name)
      return record;
  }
  return std::nullopt;
}

std::optional<VirtualCalleeRecord>
VirtualCalleeRegistry::lookupByTraceKey(uint64_t handler_va,
                                        uint64_t trace_hash) const {
  uint64_t key = traceKeyHash(handler_va, trace_hash);
  auto it = trace_key_index_.find(key);
  if (it == trace_key_index_.end())
    return std::nullopt;
  for (size_t idx : it->second) {
    const auto &r = records_[idx];
    if (r.handler_va == handler_va && r.trace_hash == trace_hash)
      return r;
  }
  return std::nullopt;
}

llvm::SmallVector<const VirtualCalleeRecord *, 4>
VirtualCalleeRegistry::lookupByBase(llvm::StringRef base_name) const {
  llvm::SmallVector<const VirtualCalleeRecord *, 4> result;
  for (const auto &record : records_) {
    if (record.base_name == base_name)
      result.push_back(&record);
  }
  return result;
}

llvm::SmallVector<const VirtualCalleeRecord *, 4>
VirtualCalleeRegistry::lookupByCaller(llvm::StringRef caller_name) const {
  llvm::SmallVector<const VirtualCalleeRecord *, 4> result;
  for (const auto &record : records_) {
    if (record.caller_name == caller_name)
      result.push_back(&record);
  }
  return result;
}

size_t VirtualCalleeRegistry::countKind(llvm::StringRef kind) const {
  size_t count = 0;
  for (const auto &record : records_) {
    if (record.kind == kind)
      ++count;
  }
  return count;
}

size_t VirtualCalleeRegistry::countTraceLinked() const {
  size_t count = 0;
  for (const auto &record : records_) {
    if (record.trace_linked)
      ++count;
  }
  return count;
}

// ---------------------------------------------------------------------------
// Trace map linkage
// ---------------------------------------------------------------------------

unsigned VirtualCalleeRegistry::linkToTraceMap(const VMTraceMap &trace_map) {
  unsigned newly_linked = 0;
  for (auto &record : records_) {
    if (record.trace_linked)
      continue;
    if (record.handler_va == 0 || !record.trace_hash)
      continue;
    auto trace = trace_map.getTraceForHash(record.handler_va, *record.trace_hash);
    if (trace) {
      record.trace_linked = true;
      ++newly_linked;
    }
  }
  return newly_linked;
}

// ---------------------------------------------------------------------------
// Index management
// ---------------------------------------------------------------------------

void VirtualCalleeRegistry::rebuildIndices() {
  trace_key_index_.clear();
  for (size_t i = 0; i < records_.size(); ++i) {
    const auto &r = records_[i];
    if (r.handler_va != 0 && r.trace_hash) {
      uint64_t key = traceKeyHash(r.handler_va, *r.trace_hash);
      trace_key_index_[key].push_back(i);
    }
  }
}

// ---------------------------------------------------------------------------
// Analysis run (deserialize from module metadata)
// ---------------------------------------------------------------------------

VirtualCalleeRegistryAnalysis::Result
VirtualCalleeRegistryAnalysis::run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
  VirtualCalleeRegistry registry;

  auto *named_md = M.getNamedMetadata(kRegistryName);
  if (!named_md)
    return registry;

  for (unsigned i = 0; i < named_md->getNumOperands(); ++i) {
    auto *tuple = named_md->getOperand(i);
    // Support both the old 6-field format and the new 9-field format.
    if (!tuple || (tuple->getNumOperands() != 6 && tuple->getNumOperands() != 9))
      continue;

    auto *clone_md = llvm::dyn_cast<llvm::MDString>(tuple->getOperand(0));
    auto *base_md = llvm::dyn_cast<llvm::MDString>(tuple->getOperand(1));
    auto *caller_md = llvm::dyn_cast<llvm::MDString>(tuple->getOperand(2));
    auto *kind_md = llvm::dyn_cast<llvm::MDString>(tuple->getOperand(3));
    auto *hash_md = llvm::dyn_cast<llvm::MDString>(tuple->getOperand(4));
    auto *round_ci =
        llvm::mdconst::dyn_extract<llvm::ConstantInt>(tuple->getOperand(5));
    if (!clone_md || !base_md || !caller_md || !kind_md || !hash_md || !round_ci)
      continue;

    VirtualCalleeRecord record;
    record.clone_name = clone_md->getString().str();
    record.base_name = base_md->getString().str();
    record.caller_name = caller_md->getString().str();
    record.kind = kind_md->getString().str();
    record.hash = parseHexString(hash_md->getString());
    record.first_round = round_ci->getZExtValue();

    // New fields (9-field format).
    if (tuple->getNumOperands() == 9) {
      if (auto *hva_ci =
              llvm::mdconst::dyn_extract<llvm::ConstantInt>(tuple->getOperand(6)))
        record.handler_va = hva_ci->getZExtValue();
      auto *trace_hash_md =
          llvm::dyn_cast<llvm::MDString>(tuple->getOperand(7));
      if (trace_hash_md)
        record.trace_hash = parseHexString(trace_hash_md->getString());
      if (auto *linked_ci =
              llvm::mdconst::dyn_extract<llvm::ConstantInt>(tuple->getOperand(8)))
        record.trace_linked = linked_ci->getZExtValue() != 0;
    }

    registry.records_.push_back(std::move(record));
  }

  registry.rebuildIndices();
  return registry;
}

// ---------------------------------------------------------------------------
// Serialization
// ---------------------------------------------------------------------------

void setVirtualCalleeRegistryMetadata(
    llvm::Module &M, llvm::ArrayRef<VirtualCalleeRecord> records) {
  auto &ctx = M.getContext();
  if (auto *old_md = M.getNamedMetadata(kRegistryName))
    M.eraseNamedMetadata(old_md);

  if (records.empty())
    return;

  auto *i64_ty = llvm::Type::getInt64Ty(ctx);
  auto *named_md = M.getOrInsertNamedMetadata(kRegistryName);
  for (const auto &record : records) {
    auto *clone_md = llvm::MDString::get(ctx, record.clone_name);
    auto *base_md = llvm::MDString::get(ctx, record.base_name);
    auto *caller_md = llvm::MDString::get(ctx, record.caller_name);
    auto *kind_md = llvm::MDString::get(ctx, record.kind);
    auto *hash_md = llvm::MDString::get(
        ctx, record.hash ? llvm::utohexstr(*record.hash) : std::string());
    auto *round_md = llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(i64_ty, record.first_round));

    // New fields for trace linkage.
    auto *handler_va_md = llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(i64_ty, record.handler_va));
    auto *trace_hash_md = llvm::MDString::get(
        ctx,
        record.trace_hash ? llvm::utohexstr(*record.trace_hash) : std::string());
    auto *linked_md = llvm::ConstantAsMetadata::get(
        llvm::ConstantInt::get(i64_ty, record.trace_linked ? 1 : 0));

    named_md->addOperand(llvm::MDTuple::get(
        ctx, {clone_md, base_md, caller_md, kind_md, hash_md, round_md,
              handler_va_md, trace_hash_md, linked_md}));
  }
}

}  // namespace omill
