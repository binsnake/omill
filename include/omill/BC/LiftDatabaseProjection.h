#pragma once

#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <vector>

#include "llvm/ADT/StringRef.h"
#include "omill/BC/LiftDatabase.h"

namespace omill {

struct LiftDbProjectionBlock {
  uint64_t entry_va = 0;
  uint64_t function_entry_va = 0;
  bool from_overlay_split = false;
  std::vector<uint64_t> instruction_vas;
  std::vector<LiftDbEdgeRecord> successors;
  std::vector<uint64_t> predecessors;
};

struct LiftDbProjection {
  enum class Kind : uint8_t {
    kFunction = 0,
    kBlock,
    kOverlay,
  };

  Kind kind = Kind::kFunction;
  uint64_t root_va = 0;
  std::string overlay_key;
  std::vector<uint64_t> block_order;
  std::map<uint64_t, LiftDbProjectionBlock> blocks;

  bool empty(void) const {
    return block_order.empty();
  }
};

const LiftDbProjectionBlock *FindProjectionBlockContaining(
    const LiftDbProjection &projection, uint64_t pc);

class LiftDatabaseProjector {
 public:
  explicit LiftDatabaseProjector(const LiftDatabase &db);

  std::optional<LiftDbProjection> projectFunction(uint64_t entry_va) const;
  std::optional<LiftDbProjection> projectBlock(uint64_t block_entry_va) const;
  std::optional<LiftDbProjection> projectOverlay(
      llvm::StringRef overlay_key) const;

 private:
  const LiftDatabase &db_;
};

}  // namespace omill
