#pragma once

/// BMIMutation — rewrite scalar expressions using x86 BMI1/BMI2 bit-manipulation
/// instructions (ANDN, BEXTR, BZHI, PDEP, PEXT, BLSI, BLSR).
///
/// Transforms:
///   XOR → ANDN pair          : x^y = (~x&y)|(~y&x)
///   OR  → De Morgan + ANDN   : x|y = ~(~x & ~y)
///   AND → nested ANDN         : x&y = ~(~y & x) & x
///   AND constant → BZHI/BEXTR : x & ((1<<n)-1) → bzhi(x, n)
///   Identity BLSI|BLSR        : x = (x & -x) | (x & (x-1))
///   Identity PDEP/PEXT        : x = pdep(pext(x,M),M) | pdep(pext(x,~M),~M)
///
/// Requires target-features +bmi (BMI1) and/or +bmi2 on the function.

#include <cstdint>

namespace llvm {
class Function;
class Module;
}  // namespace llvm

namespace ollvm {

struct FilterConfig;

bool bmiMutateFunction(llvm::Function &F, uint32_t seed,
                       const FilterConfig &cfg);

void bmiMutateModule(llvm::Module &M, uint32_t seed,
                     const FilterConfig &cfg);

}  // namespace ollvm
