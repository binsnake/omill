add_executable(omill-lift
  InputLoader.cpp
  LiftMain.cpp
  Options.cpp
  main.cpp
  RuntimeAdapters.cpp
  RecoveryBindings.cpp
)

target_link_libraries(omill-lift
  PRIVATE
    omill
    remill
    LLVMObject
    ${OMILL_LLVM_LIBS}
)

if(MSVC)
  target_link_options(omill-lift PRIVATE /STACK:16777216)
endif()

if(NOT MSVC)
  target_compile_options(omill-lift PRIVATE -fno-rtti)
endif()

# omill-lift currently lifts with kArchAMD64_AVX, so ensure the matching
# Remill semantics bitcode exists whenever this tool is built.
if(TARGET amd64_avx)
  add_dependencies(omill-lift amd64_avx)
endif()
