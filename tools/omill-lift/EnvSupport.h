#pragma once

#include <llvm/IR/Module.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Support/raw_ostream.h>

#include <optional>
#include <string>

/// Parse a boolean environment variable. Returns nullopt if unset or invalid.
/// Accepted values: "1", "t", "T" → true; "0", "f", "F" → false.
inline std::optional<bool> parseBoolEnv(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return std::nullopt;
  if ((v[0] == '1' && v[1] == '\0') ||
      (v[0] == 't' && v[1] == '\0') ||
      (v[0] == 'T' && v[1] == '\0'))
    return true;
  if ((v[0] == '0' && v[1] == '\0') ||
      (v[0] == 'f' && v[1] == '\0') ||
      (v[0] == 'F' && v[1] == '\0'))
    return false;
  return std::nullopt;
}

/// Parse an unsigned integer environment variable. Returns nullopt if unset,
/// invalid, or zero.
inline std::optional<unsigned> parseUnsignedEnv(const char *name) {
  const char *v = std::getenv(name);
  if (!v || v[0] == '\0')
    return std::nullopt;
  unsigned value = 0;
  if (llvm::StringRef(v).getAsInteger(10, value) || value == 0)
    return std::nullopt;
  return value;
}

/// Dump module IR to |path| if the boolean env variable |env_name| is set.
inline void dumpModuleIfEnvEnabled(llvm::Module &M, const char *env_name,
                                   llvm::StringRef path) {
  if (!parseBoolEnv(env_name).value_or(false))
    return;
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec, llvm::sys::fs::OF_Text);
  if (!ec)
    M.print(os, nullptr);
}

/// Append |message| to the file at OMILL_DEBUG_MARKER_FILE (if set).
inline void appendDebugMarker(const char *message) {
  const char *path = std::getenv("OMILL_DEBUG_MARKER_FILE");
  if (!path || path[0] == '\0')
    return;
  std::error_code ec;
  llvm::raw_fd_ostream os(path, ec,
                          llvm::sys::fs::OF_Append | llvm::sys::fs::OF_Text);
  if (!ec)
    os << message << "\n";
}

/// Set environment variable |name| to |value| only if it is currently unset.
inline void setEnvIfUnset(const char *name, const char *value) {
  const char *cur = std::getenv(name);
  if (cur && cur[0] != '\0')
    return;
#if defined(_WIN32)
  _putenv_s(name, value);
#else
  setenv(name, value, 0);
#endif
}

/// RAII guard that temporarily overrides an environment variable and restores
/// its previous value (or removes it) on destruction.
class ScopedEnvOverride {
 public:
  ScopedEnvOverride(const char *name, const char *value)
      : name_(name) {
    const char *cur = std::getenv(name_);
    if (cur)
      old_value_ = std::string(cur);
    had_old_value_ = cur != nullptr;
#if defined(_WIN32)
    _putenv_s(name_, value);
#else
    setenv(name_, value, 1);
#endif
  }

  ~ScopedEnvOverride() {
    if (had_old_value_) {
#if defined(_WIN32)
      _putenv_s(name_, old_value_->c_str());
#else
      setenv(name_, old_value_->c_str(), 1);
#endif
      return;
    }
#if defined(_WIN32)
    _putenv_s(name_, "");
#else
    unsetenv(name_);
#endif
  }

 private:
  const char *name_ = nullptr;
  bool had_old_value_ = false;
  std::optional<std::string> old_value_;
};
