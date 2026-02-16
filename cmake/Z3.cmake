# Download Z3 prebuilt Windows x64 binary.
include(FetchContent)

set(Z3_VERSION "4.13.4")

FetchContent_Declare(z3
  URL "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-win.zip"
  DOWNLOAD_EXTRACT_TIMESTAMP ON
)
FetchContent_MakeAvailable(z3)

# Create imported target.
add_library(z3::libz3 IMPORTED SHARED GLOBAL)
set_target_properties(z3::libz3 PROPERTIES
  IMPORTED_LOCATION "${z3_SOURCE_DIR}/bin/libz3.dll"
  IMPORTED_IMPLIB "${z3_SOURCE_DIR}/bin/libz3.lib"
  INTERFACE_INCLUDE_DIRECTORIES "${z3_SOURCE_DIR}/include"
)

message(STATUS "Z3 ${Z3_VERSION} prebuilt: ${z3_SOURCE_DIR}")
