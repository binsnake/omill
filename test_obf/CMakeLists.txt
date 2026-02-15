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
