#include <lazy_importer.hpp>
#include <xorstr.hpp>

extern "C" {
void *__stdcall LoadLibraryA(const char *);
}

#define EXPORT extern "C" __declspec(dllexport)

EXPORT int obf_combined(void **result) {
  // xorstr decrypts "user32.dll" at runtime
  auto name = xorstr("user32.dll");
  const char *p = name.crypt_get();
  // lazy_importer resolves LoadLibraryA via PEB hash walk
  auto fn = LI_FN(LoadLibraryA).get();
  *result = fn(p);
  return (*result != nullptr) ? 1 : 0;
}
