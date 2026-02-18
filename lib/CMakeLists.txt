add_library(omill STATIC
  # Utils
  Utils/IntrinsicTable.cpp
  Utils/LiftedNames.cpp
  Utils/StateFieldMap.cpp

  # Analysis
  Analysis/CallGraphAnalysis.cpp
  Analysis/LiftedFunctionMap.cpp
  Analysis/RemillIntrinsicAnalysis.cpp
  Analysis/StateFieldAccessAnalysis.cpp
  Analysis/ExceptionInfo.cpp

  # Passes - Stage 2: Intrinsic Lowering
  Passes/LowerRemillIntrinsics.cpp
  Passes/InlineJumpTargets.cpp

  # Passes - Stage 3: State Optimization
  Passes/OptimizeState.cpp
  Passes/MemoryPointerElimination.cpp

  # Passes - Stage 4: Control Flow Recovery
  Passes/ResolveForcedExceptions.cpp
  Passes/CFGRecovery.cpp

  # Analysis & Passes - Stage 5: ABI Recovery
  Analysis/CallingConventionAnalysis.cpp
  Passes/RecoverStackFrame.cpp
  Passes/RecoverFunctionSignatures.cpp
  Passes/RecoverStackFrameTypes.cpp
  Passes/RefineFunctionSignatures.cpp
  Passes/RewriteLiftedCallsToNative.cpp
  Passes/EliminateStateStruct.cpp

  # Analysis & Passes - Stage 6: Deobfuscation
  Analysis/BinaryMemoryMap.cpp
  Utils/ImportHashDB.cpp
  Passes/ConstantMemoryFolding.cpp
  Passes/HashImportAnnotation.cpp
  Passes/ResolveLazyImports.cpp
  Passes/RecoverGlobalTypes.cpp
  Passes/FoldProgramCounter.cpp
  Passes/ResolveIATCalls.cpp
  Passes/ResolveAndLowerControlFlow.cpp
  Passes/InterProceduralConstProp.cpp
  Passes/IterativeTargetResolution.cpp
  Passes/OutlineConstantStackData.cpp
  Passes/SimplifyVectorReassembly.cpp
  Passes/EliminateDeadPaths.cpp
  # Pipeline
  Pipeline.cpp
  Passes/PassRegistry.cpp
)

target_include_directories(omill
  PUBLIC
    $<BUILD_INTERFACE:${PROJECT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:${CMAKE_INSTALL_INCLUDEDIR}>
  PRIVATE
    ${PROJECT_SOURCE_DIR}/lib
)

target_link_libraries(omill
  PUBLIC
    ${OMILL_LLVM_LIBS}
)

if(OMILL_ENABLE_Z3)
  target_sources(omill PRIVATE
    Utils/SouperZ3Translator.cpp
    Utils/TranslationValidator.cpp
    Passes/Z3DispatchSolver.cpp
  )
  target_link_libraries(omill PUBLIC z3::libz3)
  target_compile_definitions(omill PUBLIC OMILL_ENABLE_Z3=1)
endif()

if(OMILL_ENABLE_SIMPLIFIER)
  target_sources(omill PRIVATE
    Simplifier/LLVMTranslator.cpp
    Passes/SimplifyMBA.cpp
  )
  target_link_libraries(omill PUBLIC eq_sat)
  target_compile_definitions(omill PUBLIC OMILL_ENABLE_SIMPLIFIER=1)
endif()

target_compile_features(omill PUBLIC cxx_std_17)

if(NOT MSVC)
  target_compile_options(omill PRIVATE
    -Wall -Wextra -Wno-unused-parameter
    -fno-rtti
  )
else()
  target_compile_options(omill PRIVATE
    /W3 /EHsc /GR-
  )
endif()
