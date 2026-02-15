# Build the EqSat Rust crate and create an imported library target.
#
# Produces:
#   eq_sat::eq_sat  - imported shared library target
#
# The Rust crate is built via `cargo build --release` in the EqSat directory.
# The resulting DLL/lib is imported so C++ code can link against it.

set(EQSAT_SOURCE_DIR "${CMAKE_SOURCE_DIR}/third_party/Simplifier/EqSat")
set(EQSAT_CARGO_TARGET_DIR "${CMAKE_BINARY_DIR}/eqsat-target")

if(WIN32)
  set(EQSAT_DLL_NAME "eq_sat.dll")
  set(EQSAT_LIB_NAME "eq_sat.dll.lib")
else()
  set(EQSAT_DLL_NAME "libeq_sat.so")
  set(EQSAT_LIB_NAME "libeq_sat.so")
endif()

set(EQSAT_DLL "${EQSAT_CARGO_TARGET_DIR}/release/${EQSAT_DLL_NAME}")
set(EQSAT_IMPLIB "${EQSAT_CARGO_TARGET_DIR}/release/${EQSAT_LIB_NAME}")

find_program(CARGO_EXECUTABLE cargo REQUIRED)

# Custom command: build the Rust crate.
add_custom_command(
  OUTPUT "${EQSAT_DLL}" "${EQSAT_IMPLIB}"
  COMMAND ${CMAKE_COMMAND} -E env
    "CARGO_TARGET_DIR=${EQSAT_CARGO_TARGET_DIR}"
    ${CARGO_EXECUTABLE} build --release
  WORKING_DIRECTORY "${EQSAT_SOURCE_DIR}"
  COMMENT "Building EqSat Rust crate (cargo build --release)"
  VERBATIM
)

# Custom target so other targets can depend on the build.
add_custom_target(eqsat_build
  DEPENDS "${EQSAT_DLL}" "${EQSAT_IMPLIB}"
)

# Imported shared library target.
add_library(eq_sat SHARED IMPORTED GLOBAL)
add_dependencies(eq_sat eqsat_build)

if(WIN32)
  set_target_properties(eq_sat PROPERTIES
    IMPORTED_LOCATION "${EQSAT_DLL}"
    IMPORTED_IMPLIB "${EQSAT_IMPLIB}"
  )
else()
  set_target_properties(eq_sat PROPERTIES
    IMPORTED_LOCATION "${EQSAT_DLL}"
  )
endif()

# Copy the DLL next to executables so they can find it at runtime.
# Call eqsat_copy_dll(<target>) to set up the copy.
function(eqsat_copy_dll target)
  add_custom_command(TARGET ${target} POST_BUILD
    COMMAND ${CMAKE_COMMAND} -E copy_if_different
      "${EQSAT_DLL}"
      "$<TARGET_FILE_DIR:${target}>/"
    COMMENT "Copying ${EQSAT_DLL_NAME} next to ${target}"
    VERBATIM
  )
endfunction()
