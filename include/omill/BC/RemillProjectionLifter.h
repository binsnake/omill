#pragma once

#include <cstdint>
#include <functional>
#include <map>
#include <optional>
#include <string>

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/StringRef.h"

namespace llvm {
class Function;
}

namespace omill {

class BlockLifter;
class LiftDatabase;
class TraceLifter;

struct RemillProjectionKey {
  enum class Kind : uint8_t {
    kFunction = 0,
    kBlock,
    kOverlay,
  };

  Kind kind = Kind::kFunction;
  uint64_t root_va = 0;
  std::string overlay_key;
};

class RemillProjectionLifter {
 public:
  RemillProjectionLifter(const LiftDatabase *db, TraceLifter &trace_lifter,
                         BlockLifter *block_lifter = nullptr);
  explicit RemillProjectionLifter(
      std::function<llvm::Function *(uint64_t,
                                     llvm::SmallVectorImpl<uint64_t> &)>
          test_block_lift_callback,
      const LiftDatabase *db = nullptr);

  bool LiftFunction(
      uint64_t entry_va,
      std::function<void(uint64_t, llvm::Function *)> callback = {});
  bool LiftOverlay(
      llvm::StringRef overlay_key,
      std::function<void(uint64_t, llvm::Function *)> callback = {});
  llvm::Function *LiftBlock(uint64_t block_va,
                            llvm::SmallVectorImpl<uint64_t> &discovered_targets);
  unsigned LiftReachable(uint64_t entry_va);
  const LiftDatabase *database(void) const { return db_; }

  llvm::Function *LookupCached(const RemillProjectionKey &key) const;

 private:
  static std::string CacheKey(const RemillProjectionKey &key);
  void CacheFunction(const RemillProjectionKey &key, llvm::Function *function);

  const LiftDatabase *db_ = nullptr;
  TraceLifter *trace_lifter_ = nullptr;
  BlockLifter *block_lifter_ = nullptr;
  std::function<llvm::Function *(uint64_t, llvm::SmallVectorImpl<uint64_t> &)>
      test_block_lift_callback_;
  std::map<std::string, llvm::Function *> cache_;
};

}  // namespace omill
