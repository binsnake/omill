// cmut value mutation/obfuscation tests.
// cmut<T> stores values in multiple mutated forms (shifted, split, SIMD-packed)
// with random shift amounts, then reconstructs via selected mode.

#include <cstddef>
#include <cstring>

// cmut.hxx uses SECURE_ZERO_MEMORY in the destructor but doesn't define it.
// Provide a volatile-memset implementation to prevent optimizer elision.
#ifndef SECURE_ZERO_MEMORY
#define SECURE_ZERO_MEMORY(ptr, cnt) do {           \
    volatile char *_p = (volatile char *)(ptr);     \
    for (size_t _i = 0; _i < (size_t)(cnt); ++_i)  \
        _p[_i] = 0;                                 \
} while(0)
#endif

#include "cmut.hxx"

#define EXPORT extern "C" __declspec(dllexport)

/// i32 constant: constructs cmut<int32_t>(42), returns reconstructed value.
/// Exercises the ui32 path (SIMD + shift-64 mutation).
EXPORT int cmut_i32_get() {
  cmut<std::int32_t> val(42);
  return val.get();
}

/// i64 constant: constructs cmut<int64_t>(0xCAFEBABE), returns reconstructed.
/// Exercises the ui64 path (split16/split32/SIMD + rotate mutation).
EXPORT long long cmut_i64_get() {
  cmut<std::int64_t> val(0xCAFEBABELL);
  return val.get();
}

/// i8 constant: constructs cmut<int8_t>('A'), returns reconstructed.
/// Exercises the ui8 path (shift-16/32/64/SIMD, 4 reconstruction modes).
EXPORT char cmut_i8_get() {
  cmut<std::int8_t> val(65);
  return static_cast<char>(val.get());
}

/// i32 passthrough: takes runtime input, mutates it, returns reconstructed.
/// Exercises the full mutation/reconstruction cycle with a runtime value
/// (prevents compile-time constant folding of the mutation).
EXPORT int cmut_i32_roundtrip(int input) {
  cmut<std::int32_t> val(input);
  return val.get();
}

/// i32 set-after-construct: constructs with 0, then set() with a new value.
/// Exercises the set() path separately from the constructor.
EXPORT int cmut_i32_set(int input) {
  cmut<std::int32_t> val(0);
  val.set(input);
  return val.get();
}
