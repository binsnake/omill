#pragma once

#include <optional>
#include <string>

#include "llvm/ADT/StringRef.h"

namespace omill {

class LiftDatabase;

bool SaveLiftDatabaseToDirectory(const LiftDatabase &db,
                                 llvm::StringRef directory,
                                 std::string *error = nullptr);

std::optional<LiftDatabase> LoadLiftDatabaseFromDirectory(
    llvm::StringRef directory, std::string *error = nullptr);

}  // namespace omill
