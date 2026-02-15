include(FetchContent)

FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG v1.14.0
)

set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

include(GoogleTest)

add_executable(omill-unit-tests
  unit/IntrinsicTableTest.cpp
  unit/LowerFlagIntrinsicsTest.cpp
  unit/LowerMemoryIntrinsicsTest.cpp
  unit/RemoveBarriersTest.cpp
  unit/DeadStateStoreEliminationTest.cpp
  unit/PromoteStateToSSATest.cpp
  unit/LowerFunctionReturnTest.cpp
  unit/CFGRecoveryTest.cpp
  unit/CallingConventionAnalysisTest.cpp
  unit/RecoverStackFrameTest.cpp
  unit/StateFieldMapTest.cpp
  unit/LowerAtomicIntrinsicsTest.cpp
  unit/LowerHyperCallsTest.cpp
  unit/LowerUndefinedIntrinsicsTest.cpp
  unit/LowerErrorAndMissingTest.cpp
  unit/LowerFunctionCallTest.cpp
  unit/LowerJumpTest.cpp
  unit/DeadStateFlagEliminationTest.cpp
  unit/MemoryPointerEliminationTest.cpp
  unit/RecoverFunctionSignaturesTest.cpp
  unit/EliminateStateStructTest.cpp
  unit/ConstantMemoryFoldingTest.cpp
  unit/ImportHashDBTest.cpp
  unit/HashImportAnnotationTest.cpp
  unit/FoldProgramCounterTest.cpp
  unit/OutlineConstantStackDataTest.cpp
  unit/LowerResolvedDispatchCallsTest.cpp
  unit/ResolveIATCallsTest.cpp
  unit/ResolveLazyImportsTest.cpp
)

target_link_libraries(omill-unit-tests
  PRIVATE
    omill
    GTest::gtest_main
    ${OMILL_LLVM_LIBS}
)

if(NOT MSVC)
  target_compile_options(omill-unit-tests PRIVATE -fno-rtti)
endif()

gtest_discover_tests(omill-unit-tests)

# E2E tests (require remill + Zydis)
if(OMILL_ENABLE_REMILL)
  FetchContent_Declare(zydis
    GIT_REPOSITORY https://github.com/zyantific/zydis.git
    GIT_TAG v4.1.0
  )
  set(ZYDIS_BUILD_TOOLS OFF CACHE BOOL "" FORCE)
  set(ZYDIS_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
  FetchContent_MakeAvailable(zydis)

  add_executable(omill-e2e-tests
    e2e/LiftAndOptFixture.cpp
    e2e/MBAPatternTest.cpp
    e2e/OpaquePredicateTest.cpp
    e2e/ControlFlowFlatteningTest.cpp
    e2e/DeobfuscationTest.cpp
  )

  # Pass the DLL path to the deobfuscation tests.
  target_compile_definitions(omill-e2e-tests PRIVATE
    OBF_TEST_DLL_PATH="${CMAKE_BINARY_DIR}/test_obf/obf_test.dll"
  )

  # Ensure the DLL is built before the tests.
  add_dependencies(omill-e2e-tests obf_test)

  target_link_libraries(omill-e2e-tests
    PRIVATE
      omill
      remill
      Zydis
      LLVMObject
      GTest::gtest_main
      ${OMILL_LLVM_LIBS}
  )

  target_include_directories(omill-e2e-tests
    PRIVATE
      ${CMAKE_CURRENT_SOURCE_DIR}/e2e
  )

  # Ensure FetchContent'd gtest headers come before remill's installed deps
  # (remill/dependencies/install/include/ has a newer gtest with ABI changes)
  get_target_property(_gtest_inc GTest::gtest INTERFACE_INCLUDE_DIRECTORIES)
  target_include_directories(omill-e2e-tests BEFORE
    PRIVATE
      ${_gtest_inc}
  )

  if(NOT MSVC)
    target_compile_options(omill-e2e-tests PRIVATE -fno-rtti)
  endif()

  gtest_discover_tests(omill-e2e-tests)
endif()
