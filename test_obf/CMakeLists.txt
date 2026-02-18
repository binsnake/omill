# Obfuscated test DLL — compiled with O2 optimizations using xorstr + lazy_importer.
# Gated behind OMILL_ENABLE_REMILL (same as e2e tests).

add_library(obf_test SHARED
  src/dllmain.cpp
  src/xorstr_funcs.cpp
  src/lazy_funcs.cpp
  src/combined_funcs.cpp
  src/mixed_funcs.cpp
  src/cloakwork_str_funcs.cpp
  src/cloakwork_import_funcs.cpp
  src/cloakwork_combined_funcs.cpp
  src/cmut_funcs.cpp
)

# Include paths for obfuscation headers.
target_include_directories(obf_test PRIVATE
  ${CMAKE_CURRENT_SOURCE_DIR}/xorstr-master/include
  ${CMAKE_CURRENT_SOURCE_DIR}/lazy_importer-master/include
  ${CMAKE_CURRENT_SOURCE_DIR}/cloakwork
  ${CMAKE_CURRENT_SOURCE_DIR}/cmut
)

# Per-file compile options: dllmain at -O0, everything else at -O2.
set_source_files_properties(src/dllmain.cpp PROPERTIES COMPILE_OPTIONS "-O0")
set_source_files_properties(
  src/xorstr_funcs.cpp
  src/lazy_funcs.cpp
  src/combined_funcs.cpp
  src/mixed_funcs.cpp
  PROPERTIES COMPILE_OPTIONS "-O2"
)

# Cloakwork requires C++20 (constinit, consteval) and -O2 for optimization.
set_source_files_properties(
  src/cloakwork_str_funcs.cpp
  src/cloakwork_import_funcs.cpp
  src/cloakwork_combined_funcs.cpp
  PROPERTIES COMPILE_OPTIONS "-O2;-std=c++20"
)

# cmut requires C++20 (<bit> for std::rotl/std::rotr) and -O2 for inlining.
set_source_files_properties(
  src/cmut_funcs.cpp
  PROPERTIES COMPILE_OPTIONS "-O2;-std=c++20"
)

# Disable AVX for xorstr to keep SIMD at SSE2 level.
target_compile_definitions(obf_test PRIVATE JM_XORSTR_DISABLE_AVX_INTRINSICS)

# Undo the global UNICODE definitions that LLVM adds — they break narrow-char
# Windows API forward declarations in the test sources.
target_compile_options(obf_test PRIVATE -UUNICODE -U_UNICODE)

# Link kernel32.lib for DllMain linkage.
target_link_libraries(obf_test PRIVATE kernel32)

# Output name without lib prefix.
set_target_properties(obf_test PROPERTIES
  PREFIX ""
  OUTPUT_NAME "obf_test"
)

# --------------------------------------------------------------------------
# OLLVM-obfuscated test DLL — C++ → bitcode → obfuscate → object → DLL.
# --------------------------------------------------------------------------

# Step 1: C++ → bitcode (at -O2 to get clean IR before obfuscation).
option(OMILL_OLLVM_OBF_FLATTEN "Enable OLLVM CFF flattening for test samples" ON)
option(OMILL_OLLVM_OBF_SUBSTITUTE "Enable OLLVM MBA substitution for test samples" ON)
option(OMILL_OLLVM_OBF_STRING_ENCRYPT "Enable OLLVM string encryption for test samples" ON)
option(OMILL_OLLVM_OBF_CONST_UNFOLD "Enable OLLVM const unfold for test samples" ON)
option(OMILL_OLLVM_OBF_VECTORIZE "Enable OLLVM scalar-to-vector transform for test samples" ON)

set(_ollvm_obf_flags "")
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
endif()

add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs.bc
  COMMAND ${CMAKE_CXX_COMPILER} -c -emit-llvm -O2
    -target x86_64-pc-windows-msvc
    ${CMAKE_CURRENT_SOURCE_DIR}/src/ollvm_funcs.cpp
    -o ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs.bc
  DEPENDS src/ollvm_funcs.cpp
  COMMENT "Compiling ollvm_funcs.cpp to bitcode"
)

# Step 2: obfuscate bitcode with ollvm-obf.
add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.bc
  COMMAND $<TARGET_FILE:ollvm-obf>
    ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs.bc
    -o ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.bc
    ${_ollvm_obf_flags}
  DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs.bc ollvm-obf
  COMMENT "Obfuscating ollvm_funcs.bc with selected OLLVM transforms: ${_ollvm_obf_flags}"
)

# Step 3: obfuscated bitcode → object (O0 to prevent LLVM undoing obfuscation).
add_custom_command(
  OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.obj
  COMMAND ${CMAKE_CXX_COMPILER} -c -O0
    -target x86_64-pc-windows-msvc
    ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.bc
    -o ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.obj
  DEPENDS ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.bc
  COMMENT "Compiling obfuscated bitcode to object"
)

# Step 4: Link DLL from obfuscated object + dllmain.
add_library(ollvm_test SHARED
  src/dllmain.cpp
  ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.obj
)
set_source_files_properties(
  ${CMAKE_CURRENT_BINARY_DIR}/ollvm_funcs_obf.obj
  PROPERTIES EXTERNAL_OBJECT TRUE GENERATED TRUE
)
set_source_files_properties(src/dllmain.cpp
  PROPERTIES COMPILE_OPTIONS "-O0"
)
target_compile_options(ollvm_test PRIVATE -UUNICODE -U_UNICODE)
target_link_libraries(ollvm_test PRIVATE kernel32)
set_target_properties(ollvm_test PROPERTIES PREFIX "" OUTPUT_NAME "ollvm_test")
add_dependencies(ollvm_test ollvm-obf)
