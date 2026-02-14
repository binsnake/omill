#include <lazy_importer.hpp>
#include <xorstr.hpp>

// Forward-declare Windows API prototypes to avoid pulling in <Windows.h>.
extern "C" {
void *__stdcall GetModuleHandleA(const char *);
void *(__stdcall *__stdcall GetProcAddress(void *, const char *))(void);
void *__stdcall VirtualAlloc(void *, unsigned long long, unsigned long,
                             unsigned long);
}

#define EXPORT extern "C" __declspec(dllexport)

/// Mixed: xorstr for module name + lazy_importer for GetModuleHandleA
/// and GetProcAddress, used together to resolve VirtualAlloc by name.
///
/// Original pattern:
///   auto kernel32 = xorstr_("kernel32.dll");
///   auto hMod = LI_FN(GetModuleHandleA)(kernel32);
///   auto pVA  = LI_FN(GetProcAddress)(hMod, xorstr_("VirtualAlloc"));
///   return pVA;
EXPORT void *obf_mixed_resolve() {
  auto hMod = LI_FN(GetModuleHandleA).get()(xorstr_("kernel32.dll"));
  auto pVA = LI_FN(GetProcAddress).get()(hMod, xorstr_("VirtualAlloc"));
  return reinterpret_cast<void *>(pVA);
}
