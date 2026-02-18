#pragma once

/// C API for the EqSat MBA simplification library (Rust cdylib).
/// Auto-generated from EqSat/src/simple_ast.rs + known_bits.rs exports.

#include <stdbool.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ---------------------------------------------------------------------------
// Opaque types
// ---------------------------------------------------------------------------

typedef struct EqSatContext EqSatContext;
typedef struct EqSatTruthTableDb EqSatTruthTableDb;

// ---------------------------------------------------------------------------
// Value types (repr(C) in Rust)
// ---------------------------------------------------------------------------

/// Index into the AST arena.  Wraps a u32.
typedef struct {
  uint32_t idx;
} EqSatAstIdx;

/// Known-bits analysis result.
typedef struct {
  uint32_t width;
  uint64_t zeroes;
  uint64_t ones;
} EqSatKnownBits;

// ---------------------------------------------------------------------------
// AST opcode constants (from get_opcode)
// ---------------------------------------------------------------------------

enum EqSatOpcode {
  EQSAT_OP_ADD = 1,
  EQSAT_OP_MUL = 2,
  EQSAT_OP_POW = 3,
  EQSAT_OP_AND = 4,
  EQSAT_OP_OR = 5,
  EQSAT_OP_XOR = 6,
  EQSAT_OP_NEG = 7,
  EQSAT_OP_LSHR = 8,
  EQSAT_OP_CONSTANT = 9,
  EQSAT_OP_SYMBOL = 10,
  EQSAT_OP_ZEXT = 11,
  EQSAT_OP_TRUNC = 12,
};

// ---------------------------------------------------------------------------
// Context lifecycle
// ---------------------------------------------------------------------------

EqSatContext *CreateContext(void);
void DestroyContext(EqSatContext *ctx);
void ContextClear(EqSatContext *ctx, EqSatAstIdx a);

// ---------------------------------------------------------------------------
// AST construction
// ---------------------------------------------------------------------------

EqSatAstIdx ContextAdd(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextMul(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextPow(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextAnd(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextOr(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextXor(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextNeg(EqSatContext *ctx, EqSatAstIdx a);
EqSatAstIdx ContextLshr(EqSatContext *ctx, EqSatAstIdx a, EqSatAstIdx b);
EqSatAstIdx ContextZext(EqSatContext *ctx, EqSatAstIdx a, uint8_t width);
EqSatAstIdx ContextTrunc(EqSatContext *ctx, EqSatAstIdx a, uint8_t width);
EqSatAstIdx ContextConstant(EqSatContext *ctx, uint64_t c, uint8_t width);
EqSatAstIdx ContextSymbol(EqSatContext *ctx, const char *s, uint8_t width);

// ---------------------------------------------------------------------------
// AST inspection
// ---------------------------------------------------------------------------

uint8_t ContextGetOpcode(const EqSatContext *ctx, EqSatAstIdx id);
uint8_t ContextGetWidth(EqSatContext *ctx, EqSatAstIdx id);
uint32_t ContextGetCost(EqSatContext *ctx, EqSatAstIdx id);
bool ContextGetHasPoly(EqSatContext *ctx, EqSatAstIdx id);
uint8_t ContextGetClass(EqSatContext *ctx, EqSatAstIdx id);
EqSatKnownBits ContextGetKnownBits(EqSatContext *ctx, EqSatAstIdx id);
uint64_t ContextGetImutData(EqSatContext *ctx, EqSatAstIdx id);
void ContextSetImutData(EqSatContext *ctx, EqSatAstIdx id, uint64_t imut);
EqSatAstIdx ContextGetOp0(const EqSatContext *ctx, EqSatAstIdx id);
EqSatAstIdx ContextGetOp1(EqSatContext *ctx, EqSatAstIdx id);
uint64_t ContextGetConstantValue(EqSatContext *ctx, EqSatAstIdx id);
char *ContextGetSymbolName(EqSatContext *ctx, EqSatAstIdx id);

// ---------------------------------------------------------------------------
// Parsing / serialization
// ---------------------------------------------------------------------------

EqSatAstIdx ContextParseAstString(EqSatContext *ctx, const char *s);
char *ContextGetAstString(EqSatContext *ctx, EqSatAstIdx id);

// ---------------------------------------------------------------------------
// Variable collection
// ---------------------------------------------------------------------------

EqSatAstIdx *ContextCollectVariables(EqSatContext *ctx, EqSatAstIdx id,
                                      uint32_t *out_len);

// ---------------------------------------------------------------------------
// Evaluation
// ---------------------------------------------------------------------------

EqSatAstIdx ContextGetBooleanForIndex(EqSatContext *ctx,
                                       const EqSatAstIdx *vars,
                                       uint32_t num_vars, uint32_t vec_idx);

EqSatAstIdx ContextGetConjunctionFromVarMask(EqSatContext *ctx,
                                              const EqSatAstIdx *vars,
                                              uint64_t var_mask);

uint64_t *ContextEvaluateForAllZeroesAndOnes(EqSatContext *ctx,
                                              EqSatAstIdx id, uint64_t mask,
                                              uint32_t *out_len);

// ---------------------------------------------------------------------------
// Simplification
// ---------------------------------------------------------------------------

EqSatAstIdx ContextSingleSimplify(EqSatContext *ctx, EqSatAstIdx idx);
EqSatAstIdx ContextRecursiveSimplify(EqSatContext *ctx, EqSatAstIdx id);

// ---------------------------------------------------------------------------
// Truth table database
// ---------------------------------------------------------------------------

EqSatTruthTableDb *CreateTruthTableDb(void);
EqSatAstIdx GetTruthTableDbEntry(EqSatTruthTableDb *db, EqSatContext *ctx,
                                  uint32_t var_count,
                                  const EqSatAstIdx *vars, EqSatAstIdx idx);
uint32_t GetTruthTableDbEntryCost(EqSatTruthTableDb *db, uint32_t var_count,
                                   EqSatAstIdx idx);

// ---------------------------------------------------------------------------
// Misc
// ---------------------------------------------------------------------------

uint64_t GetPowPtr(void);
uint64_t Pow(uint64_t base, uint64_t exp);

#ifdef __cplusplus
}  // extern "C"
#endif
