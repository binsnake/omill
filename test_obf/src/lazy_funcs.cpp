#include <lazy_importer.hpp>

// Forward-declare Windows API prototypes to avoid pulling in <Windows.h>.
extern "C" {
void *__stdcall GetModuleHandleA(const char *);
void *__stdcall VirtualAlloc(void *, unsigned long long, unsigned long,
                             unsigned long);
void *__stdcall LoadLibraryA(const char *);
}

#define EXPORT extern "C" __declspec(dllexport)

EXPORT void *obf_li_get_module_handle() {
  return reinterpret_cast<void *>(LI_FN(GetModuleHandleA).get());
}

EXPORT void *obf_li_virtual_alloc() {
  return reinterpret_cast<void *>(LI_FN(VirtualAlloc).get());
}

EXPORT void *obf_li_load_library() {
  return reinterpret_cast<void *>(LI_FN(LoadLibraryA).get());
}
