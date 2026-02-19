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

# --------------------------------------------------------------------------
# OLLVM JIT tests — compile C++ → bitcode → obfuscate → JIT → verify.
# Requires ollvm-obf tool (OMILL_ENABLE_TOOLS) but NOT remill.
# --------------------------------------------------------------------------
if(OMILL_ENABLE_TOOLS)
  option(OMILL_OLLVM_OBF_FLATTEN "Enable OLLVM CFF flattening for test samples" ON)
  option(OMILL_OLLVM_OBF_SUBSTITUTE "Enable OLLVM MBA substitution for test samples" ON)
  option(OMILL_OLLVM_OBF_STRING_ENCRYPT "Enable OLLVM string encryption for test samples" ON)
  option(OMILL_OLLVM_OBF_CONST_UNFOLD "Enable OLLVM const unfold for test samples" ON)
  option(OMILL_OLLVM_OBF_VECTORIZE "Enable OLLVM scalar-to-vector transform for test samples" ON)
  option(OMILL_OLLVM_OBF_VECTORIZE_DATA "Enable OLLVM vectorized stack data mutation for test samples" ON)
  option(OMILL_OLLVM_OBF_VECTORIZE_BITWISE "Enable OLLVM vectorized bitwise add/sub mutation for test samples" OFF)
  set(OMILL_OLLVM_OBF_SEED "2976579765" CACHE STRING "Base RNG seed for ollvm-obf test artifact generation")

  set(_ollvm_obf_flags "")
  list(APPEND _ollvm_obf_flags --seed=${OMILL_OLLVM_OBF_SEED})
  if(OMILL_OLLVM_OBF_FLATTEN)
    list(APPEND _ollvm_obf_flags --flatten)
  endif()
  if(OMILL_OLLVM_OBF_SUBSTITUTE)
    list(APPEND _ollvm_obf_flags --substitute)
  endif()
  if(OMILL_OLLVM_OBF_STRING_ENCRYPT)
    list(APPEND _ollvm_obf_flags --string-encrypt)
  endif()
  if(OMILL_OLLVM_OBF_CONST_UNFOLD)
    list(APPEND _ollvm_obf_flags --const-unfold)
  endif()
  if(OMILL_OLLVM_OBF_VECTORIZE)
    list(APPEND _ollvm_obf_flags --vectorize)
    if(OMILL_OLLVM_OBF_VECTORIZE_DATA)
      list(APPEND _ollvm_obf_flags --vectorize-data)
    else()
      list(APPEND _ollvm_obf_flags --vectorize-data=false)
    endif()
    if(OMILL_OLLVM_OBF_VECTORIZE_BITWISE)
      list(APPEND _ollvm_obf_flags --vectorize-bitwise)
    endif()
  endif()

  set(_ollvm_src "${CMAKE_CURRENT_SOURCE_DIR}/../test_obf/src/ollvm_funcs.cpp")
  set(_ollvm_clean_bc "${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_clean.bc")
  set(_ollvm_obf_bc "${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.bc")

  # Step 1: C++ → clean bitcode at -O2.
  add_custom_command(
    OUTPUT ${_ollvm_clean_bc}
    COMMAND ${CMAKE_CXX_COMPILER} -c -emit-llvm -O2
      -target x86_64-pc-windows-msvc
      ${_ollvm_src}
      -o ${_ollvm_clean_bc}
    DEPENDS ${_ollvm_src}
    COMMENT "Compiling ollvm_funcs.cpp to clean bitcode"
  )

  # Step 2: obfuscate with ollvm-obf.
  add_custom_command(
    OUTPUT ${_ollvm_obf_bc}
    COMMAND $<TARGET_FILE:ollvm-obf>
      ${_ollvm_clean_bc}
      -o ${_ollvm_obf_bc}
      ${_ollvm_obf_flags}
    DEPENDS ${_ollvm_clean_bc} ollvm-obf
    COMMENT "Obfuscating ollvm_funcs.bc with selected OLLVM transforms: ${_ollvm_obf_flags}"
  )

  # Custom target so the test binary depends on the .bc files.
  add_custom_target(ollvm_jit_bitcode
    DEPENDS ${_ollvm_clean_bc} ${_ollvm_obf_bc}
  )

  add_executable(omill-ollvm-jit-tests
    unit/OLLVMJITTest.cpp
  )

  add_dependencies(omill-ollvm-jit-tests ollvm_jit_bitcode)

  target_compile_definitions(omill-ollvm-jit-tests PRIVATE
    OLLVM_CLEAN_BC_PATH="${_ollvm_clean_bc}"
    OLLVM_OBF_BC_PATH="${_ollvm_obf_bc}"
  )

  target_link_libraries(omill-ollvm-jit-tests
    PRIVATE
      GTest::gtest_main
      ${OMILL_LLVM_LIBS}
  )

  if(NOT MSVC)
    target_compile_options(omill-ollvm-jit-tests PRIVATE -fno-rtti)
  endif()

  gtest_discover_tests(omill-ollvm-jit-tests
    PROPERTIES TIMEOUT 30
  )
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
    e2e/OLLVMTest.cpp
  )

  # Pass DLL paths to the deobfuscation tests.
  target_compile_definitions(omill-e2e-tests PRIVATE
    OBF_TEST_DLL_PATH="${CMAKE_BINARY_DIR}/test_obf/obf_test.dll"
    OLLVM_TEST_DLL_PATH="${CMAKE_BINARY_DIR}/test_obf/ollvm_test.dll"
  )

  # Ensure DLLs are built before the tests.
  add_dependencies(omill-e2e-tests obf_test ollvm_test)

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

  gtest_discover_tests(omill-e2e-tests
    PROPERTIES TIMEOUT 30
  )
endif()
