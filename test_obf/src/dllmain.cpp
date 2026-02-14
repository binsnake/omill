#include <cstdint>

using BOOL = int;
using DWORD = unsigned long;
using HINSTANCE = void *;
using LPVOID = void *;

extern "C" BOOL __stdcall DllMain(HINSTANCE, DWORD, LPVOID) {
  return 1;  // TRUE
}
