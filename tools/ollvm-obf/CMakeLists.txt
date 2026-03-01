add_executable(ollvm-obf
  ArithmeticEncoding.cpp
  BogusControlFlow.cpp
  BMIMutation.cpp
  CodeCloning.cpp
  ConstantUnfolding.cpp
  Flattening.cpp
  FunctionOutlining.cpp
  IfConversion.cpp
  InstructionScheduling.cpp
  LoopToRecursion.cpp
  main.cpp
  OpaquePredicates.cpp
  RegisterPressure.cpp
  StackRandomization.cpp
  StringEncryption.cpp
  Substitution.cpp
  Vectorize.cpp
)

target_link_libraries(ollvm-obf PRIVATE ${OMILL_LLVM_LIBS})

# ── Private (non-redistributable) passes ──────────────────────────────
# If tools/ollvm-obf/private/ exists at configure time, glob its sources
# and define OLLVM_HAS_PRIVATE so main.cpp can call into the facade.
if(IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/private")
  file(GLOB _PRIVATE_SRCS "${CMAKE_CURRENT_SOURCE_DIR}/private/*.cpp")
  if(_PRIVATE_SRCS)
    target_sources(ollvm-obf PRIVATE ${_PRIVATE_SRCS})
    target_include_directories(ollvm-obf PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}/private")
    target_compile_definitions(ollvm-obf PRIVATE OLLVM_HAS_PRIVATE)
    message(STATUS "ollvm-obf: private passes enabled")
  endif()
endif()

if(NOT MSVC)
  target_compile_options(ollvm-obf PRIVATE -fno-rtti)
endif()
