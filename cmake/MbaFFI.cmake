# Build the Mba.FFI shared library from bundled LLVM 15 Support sources.
#
# Produces:
#   mba_ffi  - shared library target (Mba.FFI.dll on Windows)
#
# The library exports FFI functions for coefficient optimization, Groebner basis,
# KnownBits analysis, and Optimal5 lookup.  It is consumed at runtime by eq_sat.dll
# via Rust raw-dylib linkage.

set(MBA_FFI_DIR "${CMAKE_SOURCE_DIR}/third_party/Simplifier/MSiMBA/Mba.FFI")

# Collect all bundled LLVM Support sources (LLVM 15, NOT system LLVM 21).
file(GLOB MBA_FFI_SUPPORT_SOURCES "${MBA_FFI_DIR}/LLVM/lib/Support/*.cpp")
# SipHash.cpp requires a header not present in the bundled LLVM and is not
# included in the upstream vcxproj — exclude it.
list(FILTER MBA_FFI_SUPPORT_SOURCES EXCLUDE REGEX "SipHash\\.cpp$")

add_library(mba_ffi SHARED
  ${MBA_FFI_SUPPORT_SOURCES}
  "${MBA_FFI_DIR}/dllmain.cpp"
)

# Override output name to match the Rust raw-dylib linkage expectation.
set_target_properties(mba_ffi PROPERTIES
  OUTPUT_NAME "Mba.FFI"
)

# Use bundled LLVM 15 headers, NOT system LLVM 21.
# The root CMakeLists.txt adds LLVM 21 system includes globally — remove them
# from this target so the bundled headers are used exclusively.
set_property(TARGET mba_ffi PROPERTY INCLUDE_DIRECTORIES "")
target_include_directories(mba_ffi PRIVATE
  "${MBA_FFI_DIR}/LLVM/include"
  "${MBA_FFI_DIR}/Groebner"
  "${MBA_FFI_DIR}"
)

target_compile_definitions(mba_ffi PRIVATE
  NDEBUG
  MBAFFI_EXPORTS
  _WINDOWS
  _USRDLL
)

target_compile_features(mba_ffi PRIVATE cxx_std_20)

target_link_libraries(mba_ffi PRIVATE Ws2_32 ntdll)

if(NOT MSVC)
  target_compile_options(mba_ffi PRIVATE
    -Wno-implicitly-unsigned-literal
  )
endif()

# Publish DLL location for other targets.
set(MBA_FFI_DLL "$<TARGET_FILE:mba_ffi>" CACHE INTERNAL "")

# Copy the DLL next to a given target's executable.
function(mba_ffi_copy_dll target)
  add_custom_command(TARGET ${target} POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
      "$<TARGET_FILE:mba_ffi>"
      "$<TARGET_FILE_DIR:${target}>/"
    COMMENT "Copying Mba.FFI.dll next to ${target}"
    VERBATIM
  )
endfunction()
