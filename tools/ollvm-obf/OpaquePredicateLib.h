#pragma once

#include <llvm/IR/GlobalVariable.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/Intrinsics.h>
#include <llvm/IR/IntrinsicsX86.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Attributes.h>
#include <llvm/IR/Value.h>

#include <cstdint>

namespace ollvm {

namespace detail {

/// Splitmix64 mixer for per-invocation coefficient derivation.
inline uint64_t mix(uint64_t &s) {
  s += 0x9e3779b97f4a7c15ULL;
  uint64_t z = s;
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

/// Build an MBA zero-expression: the result is always 0 for any x.
///
/// Uses 2-variable MBA identities with y derived from x via a random constant.
/// Four base identities (all provably zero for any x, y):
///
///   Base 0: x + y - (x ^ y) - 2*(x & y)
///   Base 1: (x | y) - (x ^ y) - (x & y)
///   Base 2: (x & y) + (x | y) - x - y
///   Base 3: 2*(x | y) - (x ^ y) - x - y
///
/// The result is multiplied by a random non-zero scale factor M to diversify
/// the constant pattern, yielding M * zero = 0.
inline llvm::Value *buildMBAZero(llvm::IRBuilder<> &builder, llvm::Value *x,
                                 uint64_t seed) {
  auto *ty = x->getType();
  uint64_t s = seed;

  // Derive y = x ^ K for a random K.
  uint64_t kRaw = mix(s) | 1;  // ensure non-zero
  auto *K = llvm::ConstantInt::get(ty, kRaw);
  auto *y = builder.CreateXor(x, K);

  // Select base identity.
  unsigned base = static_cast<unsigned>(mix(s)) % 4;

  auto *xAndY = builder.CreateAnd(x, y);
  auto *xOrY  = builder.CreateOr(x, y);
  auto *xXorY = builder.CreateXor(x, y);

  llvm::Value *zero = nullptr;
  switch (base) {
  case 0: {
    // x + y - (x ^ y) - 2*(x & y)
    auto *sum = builder.CreateAdd(x, y);
    auto *t1 = builder.CreateSub(sum, xXorY);
    auto *two = llvm::ConstantInt::get(ty, 2);
    auto *t2 = builder.CreateMul(xAndY, two);
    zero = builder.CreateSub(t1, t2);
    break;
  }
  case 1: {
    // (x | y) - (x ^ y) - (x & y)
    auto *t1 = builder.CreateSub(xOrY, xXorY);
    zero = builder.CreateSub(t1, xAndY);
    break;
  }
  case 2: {
    // (x & y) + (x | y) - x - y
    auto *t1 = builder.CreateAdd(xAndY, xOrY);
    auto *t2 = builder.CreateSub(t1, x);
    zero = builder.CreateSub(t2, y);
    break;
  }
  case 3:
  default: {
    // 2*(x | y) - (x ^ y) - x - y
    auto *two = llvm::ConstantInt::get(ty, 2);
    auto *t1 = builder.CreateMul(xOrY, two);
    auto *t2 = builder.CreateSub(t1, xXorY);
    auto *t3 = builder.CreateSub(t2, x);
    zero = builder.CreateSub(t3, y);
    break;
  }
  }

  // Scale by a random non-zero factor M to diversify constants.
  uint64_t mRaw = (mix(s) % 254) + 2;  // M ∈ [2, 255], never 0 or 1
  auto *M = llvm::ConstantInt::get(ty, mRaw);
  return builder.CreateMul(zero, M);
}

}  // namespace detail

/// Generate an opaque always-true predicate from a live integer value.
///
/// Emits a Mixed Boolean-Arithmetic (MBA) expression that always evaluates to
/// zero, then compares it using a seed-selected comparison that is guaranteed
/// true.  Each invocation varies both the MBA tree and the comparison operator
/// so no single icmp pattern fingerprints all opaque predicates.
inline llvm::Value *generateOpaqueTrue(llvm::IRBuilder<> &builder,
                                       llvm::Value *x, uint64_t seed) {
  uint64_t s = seed;
  unsigned variant = static_cast<unsigned>(detail::mix(s)) % 5;
  auto *ty = x->getType();

  switch (variant) {
  default:
  case 0: {
    // icmp eq MBA_zero, 0
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpEQ(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 1: {
    // icmp sle MBA_zero, 0  (0 <= 0 is true)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpSLE(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 2: {
    // icmp uge MBA_zero, 0  (unsigned 0 >= 0 is true)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpUGE(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 3: {
    // icmp slt MBA_zero, 1  (0 < 1 is true)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpSLT(zero, llvm::ConstantInt::get(ty, 1));
  }
  case 4: {
    // icmp eq MBA_zero_A, MBA_zero_B  (0 == 0 is true, two different trees)
    auto *zeroA = detail::buildMBAZero(builder, x, seed);
    auto *zeroB = detail::buildMBAZero(builder, x, seed ^ 0x13579BDF2468ACE0ULL);
    return builder.CreateICmpEQ(zeroA, zeroB);
  }
  }
}


/// Always-false predicate: uses seed-selected comparisons guaranteed false
/// when the MBA expression evaluates to zero.
inline llvm::Value *generateOpaqueFalse(llvm::IRBuilder<> &builder,
                                        llvm::Value *x, uint64_t seed) {
  uint64_t s = seed;
  unsigned variant = static_cast<unsigned>(detail::mix(s)) % 5;
  auto *ty = x->getType();

  switch (variant) {
  default:
  case 0: {
    // icmp ne MBA_zero, 0  (0 != 0 is false)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpNE(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 1: {
    // icmp sgt MBA_zero, 0  (0 > 0 is false)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpSGT(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 2: {
    // icmp ugt MBA_zero, 0  (unsigned 0 > 0 is false)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpUGT(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 3: {
    // icmp slt MBA_zero, 0  (0 < 0 is false)
    auto *zero = detail::buildMBAZero(builder, x, seed);
    return builder.CreateICmpSLT(zero, llvm::ConstantInt::get(ty, 0));
  }
  case 4: {
    // icmp ne MBA_zero_A, MBA_zero_B  (0 != 0 is false, two different trees)
    auto *zeroA = detail::buildMBAZero(builder, x, seed);
    auto *zeroB = detail::buildMBAZero(builder, x, seed ^ 0x13579BDF2468ACE0ULL);
    return builder.CreateICmpNE(zeroA, zeroB);
  }
  }
}

/// Generate an opaque zero from a live integer value.
/// Always evaluates to 0, but through diverse MBA arithmetic.
inline llvm::Value *generateOpaqueZero(llvm::IRBuilder<> &builder,
                                       llvm::Value *x, uint64_t seed) {
  return detail::buildMBAZero(builder, x, seed);
}

/// Software CRC32C computation (Castagnoli polynomial 0x82F63B78).
/// Matches the hardware CRC32 intrinsic result for i32 inputs.
inline uint32_t softwareCRC32C(uint32_t crc, uint32_t data) {
  crc ^= data;
  for (int i = 0; i < 32; ++i) {
    if (crc & 1)
      crc = (crc >> 1) ^ 0x82F63B78u;
    else
      crc >>= 1;
  }
  return crc;
}

/// Build an always-true predicate using the CRC32 hardware intrinsic.
///
/// Creates a volatile load from a module-level global initialized to a known
/// constant, computes CRC32 via the SSE4.2 intrinsic, and compares against the
/// precomputed expected result.  The volatile load prevents constant folding.
inline llvm::Value *buildCRC32Predicate(llvm::IRBuilder<> &builder,
                                        llvm::Function &F,
                                        uint64_t seed) {
  auto &ctx = F.getContext();
  auto *i32Ty = llvm::Type::getInt32Ty(ctx);

  // Derive two independent 32-bit constants from the seed.
  uint64_t s = seed;
  uint32_t sVal = static_cast<uint32_t>(detail::mix(s));
  uint32_t vVal = static_cast<uint32_t>(detail::mix(s));

  // Create a module-level internal global initialized to V.
  auto *module = F.getParent();
  auto *initVal = llvm::ConstantInt::get(i32Ty, vVal);
  auto *gv = new llvm::GlobalVariable(
      *module, i32Ty, /*isConstant=*/false,
      llvm::GlobalValue::InternalLinkage, initVal, "");

  // Volatile load to prevent constant folding.
  auto *loaded = builder.CreateLoad(i32Ty, gv, /*isVolatile=*/true, "");

  // Ensure the function has the CRC32 target feature so the backend can
  // select the intrinsic.  LLVM 21+ splits CRC32 into its own feature flag
  // separate from SSE4.2.  We add the full prerequisite chain plus +crc32.
  {
    llvm::StringRef features;
    if (F.hasFnAttribute("target-features"))
      features = F.getFnAttribute("target-features").getValueAsString();
    if (!features.contains("+crc32")) {
      std::string updated(features);
      for (const char *feat : {"+sse3", "+ssse3", "+sse4.1", "+sse4.2", "+crc32"}) {
        if (!llvm::StringRef(updated).contains(feat)) {
          if (!updated.empty())
            updated += ',';
          updated += feat;
        }
      }
      F.addFnAttr("target-features", updated);
    }
  }

  // Call llvm.x86.sse42.crc32.32.32(i32 S, i32 loaded_V).
  auto *seedConst = llvm::ConstantInt::get(i32Ty, sVal);
  auto *crcFn = llvm::Intrinsic::getOrInsertDeclaration(
      module, llvm::Intrinsic::x86_sse42_crc32_32_32);
  auto *crcResult = builder.CreateCall(crcFn, {seedConst, loaded}, "");

  // Precompute the expected result at compile time.
  uint32_t expected = softwareCRC32C(sVal, vVal);
  auto *expectedConst = llvm::ConstantInt::get(i32Ty, expected);

  return builder.CreateICmpEQ(crcResult, expectedConst, "");
}

}  // namespace ollvm
