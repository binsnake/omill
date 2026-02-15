// Cloakwork string encryption tests.
// Uses CW_STR (position-dependent XOR cipher) — similar pattern to xorstr.

#define CW_ENABLE_ALL 0
#define CW_ENABLE_COMPILE_TIME_RANDOM 1
#define CW_ENABLE_STRING_ENCRYPTION 1
#include <cloakwork.h>
#include <cstring>

#define EXPORT extern "C" __declspec(dllexport)

EXPORT int cw_str_hello(char *buf, int bufsize) {
  const char *p = CW_STR("Hello, World!");
  int len = 0;
  while (p[len] && len < bufsize - 1) {
    buf[len] = p[len];
    ++len;
  }
  buf[len] = '\0';
  return len;
}

EXPORT int cw_str_kernel32(char *buf, int bufsize) {
  const char *p = CW_STR("kernel32.dll");
  int len = 0;
  while (p[len] && len < bufsize - 1) {
    buf[len] = p[len];
    ++len;
  }
  buf[len] = '\0';
  return len;
}
