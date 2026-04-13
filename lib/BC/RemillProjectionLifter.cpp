#include "omill/BC/RemillProjectionLifter.h"

#include <algorithm>

#include "omill/BC/BlockLifter.h"
#include "omill/BC/LiftDatabase.h"
#include "omill/BC/LiftDatabaseProjection.h"
#include "omill/BC/TraceLifter.h"

namespace omill {
namespace {

template <typename T>
static void PushUnique(llvm::SmallVectorImpl<T> &values, const T &value) {
  if (std::find(values.begin(), values.end(), value) == values.end()) {
    values.push_back(value);
  }
}

}  // namespace

RemillProjectionLifter::RemillProjectionLifter(const LiftDatabase *db,
                                               TraceLifter &trace_lifter,
                                               BlockLifter *block_lifter)
    : db_(db), trace_lifter_(&trace_lifter), block_lifter_(block_lifter) {}

RemillProjectionLifter::RemillProjectionLifter(
    std::function<llvm::Function *(uint64_t,
                                   llvm::SmallVectorImpl<uint64_t> &)>
        test_block_lift_callback,
    const LiftDatabase *db)
    : db_(db), test_block_lift_callback_(std::move(test_block_lift_callback)) {}

std::string RemillProjectionLifter::CacheKey(const RemillProjectionKey &key) {
  switch (key.kind) {
    case RemillProjectionKey::Kind::kFunction:
      return "fn:" + std::to_string(key.root_va);
    case RemillProjectionKey::Kind::kBlock:
      return "blk:" + std::to_string(key.root_va);
    case RemillProjectionKey::Kind::kOverlay:
      return "ovl:" + key.overlay_key;
  }
  return "unknown";
}

void RemillProjectionLifter::CacheFunction(const RemillProjectionKey &key,
                                           llvm::Function *function) {
  if (!function) {
    return;
  }
  cache_[CacheKey(key)] = function;
}

llvm::Function *RemillProjectionLifter::LookupCached(
    const RemillProjectionKey &key) const {
  auto it = cache_.find(CacheKey(key));
  return it == cache_.end() ? nullptr : it->second;
}

bool RemillProjectionLifter::LiftFunction(
    uint64_t entry_va,
    std::function<void(uint64_t, llvm::Function *)> callback) {
  if (!trace_lifter_) {
    return false;
  }

  RemillProjectionKey key;
  key.kind = RemillProjectionKey::Kind::kFunction;
  key.root_va = entry_va;

  if (auto *cached = LookupCached(key)) {
    if (callback) {
      callback(entry_va, cached);
    }
    return true;
  }

  trace_lifter_->SetLiftDatabase(db_);
  trace_lifter_->SetLiftOverlayKey(std::nullopt);
  return trace_lifter_->Lift(
      entry_va, [&](uint64_t lifted_va, llvm::Function *function) {
        if (lifted_va == entry_va) {
          CacheFunction(key, function);
        }
        if (callback) {
          callback(lifted_va, function);
        }
      });
}

bool RemillProjectionLifter::LiftOverlay(
    llvm::StringRef overlay_key,
    std::function<void(uint64_t, llvm::Function *)> callback) {
  if (!db_ || !trace_lifter_) {
    return false;
  }

  auto *overlay = db_->traceOverlay(overlay_key.str());
  if (!overlay) {
    return false;
  }

  RemillProjectionKey key;
  key.kind = RemillProjectionKey::Kind::kOverlay;
  key.root_va = overlay->function_entry_va;
  key.overlay_key = overlay->overlay_key;

  if (auto *cached = LookupCached(key)) {
    if (callback) {
      callback(overlay->function_entry_va, cached);
    }
    return true;
  }

  trace_lifter_->SetLiftDatabase(db_);
  trace_lifter_->SetLiftOverlayKey(overlay->overlay_key);
  const bool lifted = trace_lifter_->Lift(
      overlay->function_entry_va,
      [&](uint64_t lifted_va, llvm::Function *function) {
        if (lifted_va == overlay->function_entry_va) {
          CacheFunction(key, function);
        }
        if (callback) {
          callback(lifted_va, function);
        }
      });
  trace_lifter_->SetLiftOverlayKey(std::nullopt);
  return lifted;
}

llvm::Function *RemillProjectionLifter::LiftBlock(
    uint64_t block_va, llvm::SmallVectorImpl<uint64_t> &discovered_targets) {
  if (!block_lifter_ && !test_block_lift_callback_) {
    return nullptr;
  }

  RemillProjectionKey key;
  key.kind = RemillProjectionKey::Kind::kBlock;
  key.root_va = block_va;

  if (auto *cached = LookupCached(key)) {
    discovered_targets.clear();
    if (db_) {
      LiftDatabaseProjector projector(*db_);
      if (auto projection = projector.projectBlock(block_va)) {
        if (auto block_it = projection->blocks.find(block_va);
            block_it != projection->blocks.end()) {
          for (const auto &edge : block_it->second.successors) {
            if (!edge.target_block_va) {
              continue;
            }
            switch (edge.kind) {
              case LiftDbEdgeKind::kFallthrough:
              case LiftDbEdgeKind::kBranchTaken:
              case LiftDbEdgeKind::kOverlay:
                PushUnique(discovered_targets, edge.target_block_va);
                break;
              default:
                break;
            }
          }
        }
      }
    }
    return cached;
  }

  llvm::Function *function = nullptr;
  if (block_lifter_) {
    block_lifter_->SetLiftDatabase(db_);
    function = block_lifter_->LiftBlock(block_va, discovered_targets);
  } else {
    function = test_block_lift_callback_(block_va, discovered_targets);
  }
  CacheFunction(key, function);
  return function;
}

unsigned RemillProjectionLifter::LiftReachable(uint64_t entry_va) {
  if (!block_lifter_) {
    return 0;
  }

  block_lifter_->SetLiftDatabase(db_);
  return block_lifter_->LiftReachable(entry_va);
}

}  // namespace omill
