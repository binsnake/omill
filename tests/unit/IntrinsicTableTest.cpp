#include "omill/Utils/IntrinsicTable.h"

#include <llvm/IR/Function.h>
#include <llvm/IR/IRBuilder.h>
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>

#include <gtest/gtest.h>

namespace {

class IntrinsicTableTest : public ::testing::Test {
 protected:
  llvm::LLVMContext Ctx;

  /// Create a module with some remill-style intrinsic declarations.
  std::unique_ptr<llvm::Module> createModuleWithIntrinsics() {
    auto M = std::make_unique<llvm::Module>("test", Ctx);

    auto *i8_ty = llvm::Type::getInt8Ty(Ctx);
    auto *i16_ty = llvm::Type::getInt16Ty(Ctx);
    auto *i32_ty = llvm::Type::getInt32Ty(Ctx);
    auto *i64_ty = llvm::Type::getInt64Ty(Ctx);
    auto *ptr_ty = llvm::PointerType::get(Ctx, 0);
    auto *i1_ty = llvm::Type::getInt1Ty(Ctx);

    // Memory read: uint8_t __remill_read_memory_8(Memory*, addr_t)
    llvm::FunctionType::get(i8_ty, {ptr_ty, i64_ty}, false);
    M->getOrInsertFunction(
        "__remill_read_memory_8",
        llvm::FunctionType::get(i8_ty, {ptr_ty, i64_ty}, false));

    // Memory write: Memory* __remill_write_memory_32(Memory*, addr_t, uint32_t)
    M->getOrInsertFunction(
        "__remill_write_memory_32",
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, i32_ty}, false));

    // Flag computation: bool __remill_flag_computation_zero(bool, ...)
    M->getOrInsertFunction(
        "__remill_flag_computation_zero",
        llvm::FunctionType::get(i1_ty, {i1_ty}, true));

    // Control flow: Memory* __remill_function_call(State&, addr_t, Memory*)
    M->getOrInsertFunction(
        "__remill_function_call",
        llvm::FunctionType::get(ptr_ty, {ptr_ty, i64_ty, ptr_ty}, false));

    // Barrier: Memory* __remill_barrier_load_store(Memory*)
    M->getOrInsertFunction(
        "__remill_barrier_load_store",
        llvm::FunctionType::get(ptr_ty, {ptr_ty}, false));

    return M;
  }
};

TEST_F(IntrinsicTableTest, ClassifiesKnownIntrinsics) {
  auto M = createModuleWithIntrinsics();
  omill::IntrinsicTable table(*M);

  auto *read8 = M->getFunction("__remill_read_memory_8");
  ASSERT_NE(read8, nullptr);
  EXPECT_EQ(table.classify(read8), omill::IntrinsicKind::kReadMemory8);
  EXPECT_TRUE(table.isRemillIntrinsic(read8));

  auto *write32 = M->getFunction("__remill_write_memory_32");
  ASSERT_NE(write32, nullptr);
  EXPECT_EQ(table.classify(write32), omill::IntrinsicKind::kWriteMemory32);

  auto *flag_zero = M->getFunction("__remill_flag_computation_zero");
  ASSERT_NE(flag_zero, nullptr);
  EXPECT_EQ(table.classify(flag_zero),
            omill::IntrinsicKind::kFlagComputationZero);

  auto *func_call = M->getFunction("__remill_function_call");
  ASSERT_NE(func_call, nullptr);
  EXPECT_EQ(table.classify(func_call), omill::IntrinsicKind::kFunctionCall);
}

TEST_F(IntrinsicTableTest, CategoriesAreCorrect) {
  auto M = createModuleWithIntrinsics();
  omill::IntrinsicTable table(*M);

  auto *read8 = M->getFunction("__remill_read_memory_8");
  EXPECT_EQ(table.category(read8), omill::IntrinsicCategory::kMemoryRead);

  auto *write32 = M->getFunction("__remill_write_memory_32");
  EXPECT_EQ(table.category(write32), omill::IntrinsicCategory::kMemoryWrite);

  auto *barrier = M->getFunction("__remill_barrier_load_store");
  EXPECT_EQ(table.category(barrier), omill::IntrinsicCategory::kBarrier);
}

TEST_F(IntrinsicTableTest, UnknownFunctionsReturnUnknown) {
  auto M = createModuleWithIntrinsics();

  // Add a non-remill function
  M->getOrInsertFunction(
      "my_function",
      llvm::FunctionType::get(llvm::Type::getVoidTy(Ctx), false));

  omill::IntrinsicTable table(*M);

  auto *my_func = M->getFunction("my_function");
  EXPECT_EQ(table.classify(my_func), omill::IntrinsicKind::kUnknown);
  EXPECT_FALSE(table.isRemillIntrinsic(my_func));
}

TEST_F(IntrinsicTableTest, GetByKindWorks) {
  auto M = createModuleWithIntrinsics();
  omill::IntrinsicTable table(*M);

  auto *read8 = table.get(omill::IntrinsicKind::kReadMemory8);
  ASSERT_NE(read8, nullptr);
  EXPECT_EQ(read8->getName(), "__remill_read_memory_8");

  // Non-existent intrinsic
  auto *read16 = table.get(omill::IntrinsicKind::kReadMemory16);
  EXPECT_EQ(read16, nullptr);
}

}  // namespace
