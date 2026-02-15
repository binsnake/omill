// Cloakwork combined: string encryption + import hiding + value obfuscation.

#define CW_ENABLE_ALL 0
#define CW_ENABLE_COMPILE_TIME_RANDOM 1
#define CW_ENABLE_STRING_ENCRYPTION 1
#define CW_ENABLE_IMPORT_HIDING 1
#define CW_ENABLE_VALUE_OBFUSCATION 1
#include <cloakwork.h>

// cloakwork.h includes Windows headers when import hiding is enabled.

#define EXPORT extern "C" __declspec(dllexport)

/// Combined: CW_STR decrypts "user32.dll", CW_IMPORT resolves LoadLibraryA.
EXPORT int cw_combined(void **result) {
  const char *name = CW_STR("user32.dll");
  auto fn = CW_IMPORT("kernel32.dll", LoadLibraryA);
  *result = fn(name);
  return (*result != nullptr) ? CW_INT(1) : CW_INT(0);
}
