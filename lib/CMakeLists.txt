add_library(omill STATIC
  # Arch
  Arch/ArchABI.cpp

  # Devirtualization
  Devirtualization/Orchestrator.cpp
  Devirtualization/OutputRootClosure.cpp
  Remill/Normalization.cpp

  # Utils
  Utils/IntrinsicTable.cpp
  Utils/LiftedNames.cpp
  Utils/ProtectedBoundaryUtils.cpp
  Utils/StateFieldMap.cpp
  Tools/LiftRunContract.cpp

  # Analysis
  Analysis/TargetArchAnalysis.cpp
  Analysis/CallGraphAnalysis.cpp
  Analysis/LiftedFunctionMap.cpp
  Analysis/IterativeLiftingSession.cpp
  Analysis/RemillIntrinsicAnalysis.cpp
  Analysis/StateFieldAccessAnalysis.cpp
  Analysis/VirtualModel/CallSites.cpp
  Analysis/VirtualModel/CallState.cpp
  Analysis/VirtualModel/Core.cpp
  Analysis/VirtualModel/Dispatch.cpp
  Analysis/VirtualModel/DirectCallees.cpp
  Analysis/VirtualModel/Driver.cpp
  Analysis/VirtualModel/Facts.cpp
  Analysis/VirtualModel/Imports.cpp
  Analysis/VirtualModel/LocalizedCalls.cpp
  Analysis/VirtualModel/Localization.cpp
  Analysis/VirtualModel/Model.cpp
  Analysis/VirtualModel/PropagationCache.cpp
  Analysis/VirtualModel/Propagation.cpp
  Analysis/VirtualModel/Replay.cpp
  Analysis/VirtualModel/Regions.cpp
  Analysis/VirtualModel/Render.cpp
      Analysis/VirtualModel/RootSlices.cpp
      Analysis/VirtualModel/StackFactTracker.cpp
      Analysis/VirtualModel/StateFacts.cpp
      Analysis/VirtualModel/Specialization.cpp
      Analysis/VirtualModel/Summary.cpp
      Analysis/VirtualModel/Targets.cpp
  Analysis/VirtualModel/Transfers.cpp
  Analysis/VirtualModel/ValueExprs.cpp
  Analysis/VirtualModel/VIP.cpp
  Analysis/ExceptionInfo.cpp
  Analysis/SegmentsAA.cpp
  Analysis/VirtualCalleeRegistry.cpp

  # Passes - Stage 2: Intrinsic Lowering
  Passes/LowerRemillIntrinsics.cpp
  Passes/InlineJumpTargets.cpp

  # Passes - Stage 3: State Optimization
  Passes/OptimizeState.cpp
  Passes/MemoryPointerElimination.cpp

  # Passes - Stage 2.5: VM Devirtualization
  Analysis/VMTraceMap.cpp
  Analysis/VMTraceEmulator.cpp
  Passes/VMDispatchResolution.cpp
  Passes/VMDeadMergedHandlerElimination.cpp

  # Passes - Stage 4: Control Flow Recovery
  Passes/ResolveForcedExceptions.cpp
  Passes/CFGRecovery.cpp

  # Analysis & Passes - Stage 5: ABI Recovery
  Analysis/CallingConventionAnalysis.cpp
  Passes/RecoverStackFrame.cpp
  Passes/RecoverStackFrameTypes.cpp

  # Analysis & Passes - Stage 6: Deobfuscation
  Analysis/BinaryMemoryMap.cpp
  Utils/ImportHashDB.cpp
  Passes/ConstantMemoryFolding.cpp
  Passes/CombinedFixedPointDevirt.cpp
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
  Passes/MemoryCoalesce.cpp
  Passes/PartialOverlapDSE.cpp
  Passes/KnownIndexSelect.cpp
  Passes/PointersHoisting.cpp
  Passes/JunkInstructionRemover.cpp
  Passes/JumpTableConcretizer.cpp
  Passes/IndirectCallResolver.cpp
  Passes/ControlFlowUnflattener.cpp
  Passes/SynthesizeFlags.cpp
  Passes/StackConcretization.cpp
  Passes/DeadStateStoreDSE.cpp
  Passes/ExpandI128DivRem.cpp
  Passes/StripCompilerUsed.cpp
  Passes/EliminateDeadTraceCounters.cpp
  Passes/MergeBytePhis.cpp
  Passes/CollapseRemillSHRSwitch.cpp
  Passes/RecoverAllocaPointers.cpp
  Passes/TypeRecovery.cpp
  Passes/VirtualCFGMaterialization.cpp
  Passes/VMHandlerInliner.cpp
  Passes/IterativeBlockDiscovery.cpp
  Passes/MergeBlockFunctions.cpp
  BC/BlockLifterAnalysis.cpp
  BC/TraceLiftAnalysis.cpp
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

# Ported remill TraceLifter + BlockLifter (only when remill is available)
if(OMILL_ENABLE_REMILL)
  target_sources(omill PRIVATE
    BC/TraceLifter.cpp
    BC/BlockLifter.cpp
  )
  target_link_libraries(omill PRIVATE remill)
  target_compile_definitions(omill PUBLIC OMILL_ENABLE_REMILL=1)
endif()
