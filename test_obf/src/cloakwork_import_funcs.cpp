// Cloakwork import hiding tests.
// Uses CW_IMPORT (PEB walking with FNV-1a hashing) — similar to lazy_importer.

#define CW_ENABLE_ALL 0
#define CW_ENABLE_COMPILE_TIME_RANDOM 1
#define CW_ENABLE_IMPORT_HIDING 1
#include <cloakwork.h>

// cloakwork.h includes Windows headers when import hiding is enabled,
// so no need for forward declarations — the real prototypes are available.

#define EXPORT extern "C" __declspec(dllexport)

EXPORT void *cw_import_get_module_handle() {
  auto fn = CW_IMPORT("kernel32.dll", GetModuleHandleA);
  return reinterpret_cast<void *>(fn);
}

EXPORT void *cw_import_virtual_alloc() {
  auto fn = CW_IMPORT("kernel32.dll", VirtualAlloc);
  return reinterpret_cast<void *>(fn);
}

EXPORT void *cw_import_load_library() {
  auto fn = CW_IMPORT("kernel32.dll", LoadLibraryA);
  return reinterpret_cast<void *>(fn);
}
