cmake_minimum_required(VERSION 3.21)

project(omill
  VERSION 0.1.0
  LANGUAGES C CXX
)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

include(GNUInstallDirs)
include("${CMAKE_CURRENT_SOURCE_DIR}/cmake/options.cmake")

# LLVM
find_package(LLVM CONFIG REQUIRED)
message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

include_directories(SYSTEM ${LLVM_INCLUDE_DIRS})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})

llvm_map_components_to_libnames(OMILL_LLVM_LIBS ${OMILL_LLVM_COMPONENTS})
message(STATUS "LLVM libraries: ${OMILL_LLVM_LIBS}")

# Fix DIA SDK path if LLVM was built against a different VS version.
if(TARGET LLVMDebugInfoPDB)
  get_target_property(_pdb_libs LLVMDebugInfoPDB INTERFACE_LINK_LIBRARIES)
  if(_pdb_libs)
    string(REPLACE
      "C:/Program Files (x86)/Microsoft Visual Studio/2019/Professional/DIA SDK/lib/amd64/diaguids.lib"
      "C:/Program Files/Microsoft Visual Studio/2022/Community/DIA SDK/lib/amd64/diaguids.lib"
      _pdb_libs_fixed "${_pdb_libs}")
    if(NOT "${_pdb_libs}" STREQUAL "${_pdb_libs_fixed}")
      set_target_properties(LLVMDebugInfoPDB PROPERTIES
        INTERFACE_LINK_LIBRARIES "${_pdb_libs_fixed}")
      message(STATUS "Patched LLVMDebugInfoPDB DIA SDK path for VS2022")
    endif()
  endif()
endif()

# Remill integration (optional, for e2e testing)
if(OMILL_ENABLE_REMILL)
  # Find remill's dependencies (installed by its superbuild in
  # third_party/remill/dependencies/install/)
  # Order matters: gflags first (glog depends on it), then glog, then XED.
  set(GFLAGS_USE_TARGET_NAMESPACE ON)
  find_package(gflags CONFIG REQUIRED)
  find_package(glog CONFIG REQUIRED)
  find_package(XED CONFIG REQUIRED)

  # Minimize remill build — we only need the library, not tests/install
  set(REMILL_ENABLE_TESTING OFF CACHE BOOL "" FORCE)
  set(REMILL_ENABLE_INSTALL_TARGET OFF CACHE BOOL "" FORCE)
  set(REMILL_BUILD_SPARC32_RUNTIME OFF CACHE BOOL "" FORCE)

  add_subdirectory(third_party/remill)
  add_subdirectory(test_obf)
  message(STATUS "Remill enabled for e2e testing")
else()
  message(STATUS "Remill disabled (set -DOMILL_ENABLE_REMILL=ON to enable e2e tests)")
endif()

# Z3 constraint-based dispatch solver (optional)
if(OMILL_ENABLE_Z3)
  include("${CMAKE_CURRENT_SOURCE_DIR}/cmake/Z3.cmake")
  message(STATUS "Z3 dispatch solver enabled")
else()
  message(STATUS "Z3 disabled (set -DOMILL_ENABLE_Z3=ON to enable)")
endif()

# EqSat MBA simplifier (optional, Rust crate)
if(OMILL_ENABLE_SIMPLIFIER)
  include("${CMAKE_CURRENT_SOURCE_DIR}/cmake/EqSat.cmake")
  message(STATUS "EqSat simplifier enabled (cargo build)")
else()
  message(STATUS "EqSat simplifier disabled (set -DOMILL_ENABLE_SIMPLIFIER=ON to enable)")
endif()

# omill library
add_subdirectory(lib)

# Tools
if(OMILL_ENABLE_TOOLS)
  add_subdirectory(tools/omill-opt)
  add_subdirectory(tools/ollvm-obf)
  if(OMILL_ENABLE_REMILL)
    add_subdirectory(tools/omill-lift)
  endif()
endif()

# Tests
if(OMILL_ENABLE_TESTING)
  enable_testing()
  add_subdirectory(tests)
endif()
