#include "RandomIRVerifier.h"

#include <gtest/gtest.h>

#include <cstdlib>

#if OMILL_ENABLE_Z3

namespace {

class FuzzSemanticVerificationTest : public ::testing::Test {
 protected:
  z3::context Z3Ctx;

  unsigned getIterations() {
    if (auto *env = std::getenv("OMILL_FUZZ_ITERATIONS"))
      return (unsigned)std::atoi(env);
    return 100;
  }
};

TEST_F(FuzzSemanticVerificationTest, CoalesceByteReassembly) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 0 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::CoalesceByteReassembly, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

TEST_F(FuzzSemanticVerificationTest, CollapsePartialXMMWrites) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 1 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::CollapsePartialXMMWrites, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

TEST_F(FuzzSemanticVerificationTest, SimplifyVectorFlagComputation) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 2 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::SimplifyVectorFlagComputation, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

TEST_F(FuzzSemanticVerificationTest, DeadStateRoundtripElimination) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 3 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::DeadStateRoundtripElimination, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

TEST_F(FuzzSemanticVerificationTest, EliminateRedundantByteStores) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 4 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::EliminateRedundantByteStores, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

TEST_F(FuzzSemanticVerificationTest, FoldConstantVectorChains) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 5 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::FoldConstantVectorChains, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

TEST_F(FuzzSemanticVerificationTest, OutlineConstantStackData) {
  unsigned iters = getIterations();
  omill::test::RandomIRVerifier fuzzer(Z3Ctx, 6 * 1000);
  auto result = fuzzer.fuzzPass(
      omill::test::PassKind::OutlineConstantStackData, iters);
  EXPECT_TRUE(result.all_passed) << result.first_failure;
  EXPECT_GT(result.num_tested, 0u);
}

}  // namespace

#endif  // OMILL_ENABLE_Z3
