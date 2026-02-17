include(FetchContent)

FetchContent_Declare(
  googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG v1.14.0
)

set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

# Zydis disassembler (used by codegen unit tests and e2e tests)
FetchContent_Declare(zydis
  GIT_REPOSITORY https://github.com/zyantific/zydis.git
  GIT_TAG v4.1.0
)
set(ZYDIS_BUILD_TOOLS OFF CACHE BOOL "" FORCE)
set(ZYDIS_BUILD_EXAMPLES OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(zydis)

include(GoogleTest)

# Map LLVMObject for COFF parsing in codegen tests
llvm_map_components_to_libnames(_llvm_object_lib Object)

add_executable(omill-unit-tests
  unit/CallGraphAnalysisTest.cpp
  unit/InterProceduralConstPropTest.cpp
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
  unit/RecoverStackFrameTypesTest.cpp
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
  unit/RefineFunctionSignaturesTest.cpp
  unit/EliminateStateStructTest.cpp
  unit/ConstantMemoryFoldingTest.cpp
  unit/ImportHashDBTest.cpp
  unit/HashImportAnnotationTest.cpp
  unit/FoldProgramCounterTest.cpp
  unit/OutlineConstantStackDataTest.cpp
  unit/LowerResolvedDispatchCallsTest.cpp
  unit/ResolveIATCallsTest.cpp
  unit/ResolveLazyImportsTest.cpp
  unit/RecoverGlobalTypesTest.cpp
  unit/ResolveDispatchTargetsTest.cpp
  unit/RecoverJumpTablesTest.cpp
  unit/SymbolicJumpTableSolverTest.cpp
  unit/EliminateDeadPathsTest.cpp
  unit/HyperCallCodegenTest.cpp
  unit/IterativeTargetResolutionTest.cpp
  unit/PassRegistryTest.cpp
  unit/RewriteLiftedCallsToNativeTest.cpp
  unit/ResolveForcedExceptionsTest.cpp
  unit/SimplifyVectorFlagComputationTest.cpp
  unit/CollapsePartialXMMWritesTest.cpp
  unit/CoalesceByteReassemblyTest.cpp
  unit/FoldConstantVectorChainsTest.cpp
  unit/DeadStateRoundtripEliminationTest.cpp
  unit/EliminateRedundantByteStoresTest.cpp
  unit/ResolveNativeDispatchTest.cpp
)

target_link_libraries(omill-unit-tests
  PRIVATE
    omill
    Zydis
    GTest::gtest_main
    ${OMILL_LLVM_LIBS}
    ${_llvm_object_lib}
)

target_include_directories(omill-unit-tests
  PRIVATE
    ${CMAKE_CURRENT_SOURCE_DIR}/utils
)

if(NOT MSVC)
  target_compile_options(omill-unit-tests PRIVATE -fno-rtti)
endif()

if(OMILL_ENABLE_Z3)
  target_sources(omill-unit-tests PRIVATE
    unit/LLVMZ3TranslatorTest.cpp
    unit/Z3DispatchSolverTest.cpp
    unit/TranslationValidationTest.cpp
    unit/SemanticVerificationTest.cpp
    unit/FuzzSemanticVerificationTest.cpp
    unit/RandomIRVerifier.cpp
  )
  # Copy libz3.dll next to the test binary so it can be found at runtime.
  add_custom_command(TARGET omill-unit-tests POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
      "${z3_SOURCE_DIR}/bin/libz3.dll"
      "$<TARGET_FILE_DIR:omill-unit-tests>/libz3.dll"
  )
endif()

if(OMILL_ENABLE_SIMPLIFIER)
  target_sources(omill-unit-tests PRIVATE unit/SimplifyMBATest.cpp)
  eqsat_copy_dll(omill-unit-tests)
  # Use PRE_TEST discovery so the exe isn't run at build time (requires
  # Mba.FFI.dll which may not be available during the build step).
  gtest_discover_tests(omill-unit-tests DISCOVERY_MODE PRE_TEST)
else()
  gtest_discover_tests(omill-unit-tests)
endif()

# E2E tests (require remill + Zydis)
if(OMILL_ENABLE_REMILL)
  add_executable(omill-e2e-tests
    e2e/LiftAndOptFixture.cpp
    e2e/MBAPatternTest.cpp
    e2e/OpaquePredicateTest.cpp
    e2e/ControlFlowFlatteningTest.cpp
    e2e/DeobfuscationTest.cpp
    e2e/HyperCallRoundTripTest.cpp
    e2e/ForcedExceptionTest.cpp
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
      ${_llvm_object_lib}
      GTest::gtest_main
      ${OMILL_LLVM_LIBS}
  )

  target_include_directories(omill-e2e-tests
    PRIVATE
      ${CMAKE_CURRENT_SOURCE_DIR}/e2e
      ${CMAKE_CURRENT_SOURCE_DIR}/utils
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
