add_library(ollvm-plugin MODULE
  OllvmPlugin.cpp
  # Include obfuscation pass sources directly — plugin is standalone.
  ../ollvm-obf/Flattening.cpp
  ../ollvm-obf/Substitution.cpp
  ../ollvm-obf/StringEncryption.cpp
  ../ollvm-obf/ConstantUnfolding.cpp
  ../ollvm-obf/Vectorize.cpp
  ../ollvm-obf/OpaquePredicates.cpp
  ../ollvm-obf/BogusControlFlow.cpp
)

target_include_directories(ollvm-plugin PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/../ollvm-obf
)

# ── Private (non-redistributable) passes ──────────────────────────────
set(_PRIVATE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../ollvm-obf/private")
if(IS_DIRECTORY "${_PRIVATE_DIR}")
  file(GLOB _PRIVATE_SRCS "${_PRIVATE_DIR}/*.cpp")
  if(_PRIVATE_SRCS)
    target_sources(ollvm-plugin PRIVATE ${_PRIVATE_SRCS})
    target_include_directories(ollvm-plugin PRIVATE "${_PRIVATE_DIR}")
    target_compile_definitions(ollvm-plugin PRIVATE OLLVM_HAS_PRIVATE)
    message(STATUS "ollvm-plugin: private passes enabled")
  endif()
endif()

target_link_libraries(ollvm-plugin PRIVATE ${OMILL_LLVM_LIBS})
target_compile_features(ollvm-plugin PUBLIC cxx_std_17)

target_compile_options(ollvm-plugin PRIVATE -fno-rtti)
if(NOT WIN32)
  target_compile_options(ollvm-plugin PRIVATE -fPIC)
endif()

set_target_properties(ollvm-plugin PROPERTIES
  PREFIX ""
  OUTPUT_NAME "OllvmPlugin"
)