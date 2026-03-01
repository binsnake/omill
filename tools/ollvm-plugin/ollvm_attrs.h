/// @file ollvm_attrs.h
/// Per-function obfuscation attributes for use with OllvmPlugin.
///
/// Include this header and annotate functions:
///
///   OLLVM_ALL void critical_func(void) { ... }
///   OLLVM_FLATTEN OLLVM_INDIRECT_CALLS int compute(int x) { ... }
///
/// Compile with:
///   clang -fpass-plugin=OllvmPlugin.dll -O2 ...
///
/// Default-enable passes for ALL functions (no annotations needed):
///
///   set OLLVM_DEFAULTS=opaque-constants,indirect-calls
///   set OLLVM_SEED=42
///   clang -fpass-plugin=OllvmPlugin.dll -O2 foo.c
///
/// Or enable everything:
///
///   set OLLVM_DEFAULTS=all
///
/// OLLVM_NONE opts a function out of everything, including defaults.
///
/// Valid pass names for OLLVM_DEFAULTS:
///   flatten, substitute, string-encrypt, const-unfold, vectorize,
///   opaque-predicates, bogus-cf, dead-memory, opaque-addressing,
///   entangle-arithmetic, opaque-constants, encode-literals,
///   indirect-calls, cfi-poisoning, anti-symbolic, all

#pragma once

#define OLLVM_ATTR(tag)  __attribute__((annotate(tag)))

// Meta
#define OLLVM_ALL                   OLLVM_ATTR("ollvm_all")
#define OLLVM_NONE                  OLLVM_ATTR("ollvm_none")

// Public passes (always available)
#define OLLVM_FLATTEN               OLLVM_ATTR("ollvm_flatten")
#define OLLVM_SUBSTITUTE            OLLVM_ATTR("ollvm_substitute")
#define OLLVM_STRING_ENCRYPT        OLLVM_ATTR("ollvm_string_encrypt")
#define OLLVM_CONST_UNFOLD          OLLVM_ATTR("ollvm_const_unfold")
#define OLLVM_VECTORIZE             OLLVM_ATTR("ollvm_vectorize")
#define OLLVM_OPAQUE_PREDICATES     OLLVM_ATTR("ollvm_opaque_predicates")
#define OLLVM_BOGUS_CF              OLLVM_ATTR("ollvm_bogus_cf")

// Private passes (requires private/ build)
#define OLLVM_DEAD_MEMORY           OLLVM_ATTR("ollvm_dead_memory")
#define OLLVM_OPAQUE_ADDRESSING     OLLVM_ATTR("ollvm_opaque_addressing")
#define OLLVM_ENTANGLE_ARITHMETIC   OLLVM_ATTR("ollvm_entangle_arithmetic")
#define OLLVM_OPAQUE_CONSTANTS      OLLVM_ATTR("ollvm_opaque_constants")
#define OLLVM_ENCODE_LITERALS       OLLVM_ATTR("ollvm_encode_literals")
#define OLLVM_INDIRECT_CALLS        OLLVM_ATTR("ollvm_indirect_calls")
#define OLLVM_CFI_POISONING         OLLVM_ATTR("ollvm_cfi_poisoning")
#define OLLVM_ANTI_SYMBOLIC         OLLVM_ATTR("ollvm_anti_symbolic")
