#include <xorstr.hpp>
#include <cstring>

#define EXPORT extern "C" __declspec(dllexport)

// Write the decrypted xorstr into a caller-provided buffer.
// Use xorstr() to keep the xor_string object alive, then crypt_get()
// to decrypt in-place before copying out.
EXPORT int obf_xorstr_hello(char *buf, int bufsize) {
  auto s = xorstr("Hello, World!");
  const char *p = s.crypt_get();
  int len = 0;
  while (p[len] && len < bufsize - 1) {
    buf[len] = p[len];
    ++len;
  }
  buf[len] = '\0';
  return len;
}

EXPORT int obf_xorstr_kernel32(char *buf, int bufsize) {
  auto s = xorstr("kernel32.dll");
  const char *p = s.crypt_get();
  int len = 0;
  while (p[len] && len < bufsize - 1) {
    buf[len] = p[len];
    ++len;
  }
  buf[len] = '\0';
  return len;
}
