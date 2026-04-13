option(OMILL_ENABLE_TESTING "Build omill tests" ON)
option(OMILL_ENABLE_TOOLS "Build omill-opt CLI tool" ON)
option(OMILL_ENABLE_REMILL "Build with remill for e2e testing" OFF)
option(OMILL_ENABLE_SIMPLIFIER "Build with EqSat MBA simplifier" OFF)
option(OMILL_ENABLE_Z3 "Build with Z3 constraint-based dispatch solver" OFF)
option(OMILL_ENABLE_UNICORN "Build with Unicorn engine for VMP return-address redirect analysis" OFF)
set(OMILL_UNICORN_DIR "" CACHE PATH "Path to unicorn install (containing include/ and lib/)")
option(OMILL_AUTO_FETCH_QT
  "Automatically download Qt6 for omill-lift-ui when Qt6 is not installed"
  ON)

set(OMILL_QT_VERSION "6.8.2" CACHE STRING
  "Qt version used by omill-lift-ui auto-fetch")
set(OMILL_QT_ARCH "win64_msvc2022_64" CACHE STRING
  "Qt architecture package used by omill-lift-ui auto-fetch")
set(OMILL_QT_MODULES "" CACHE STRING
  "Semicolon-separated Qt modules to install with aqt")
set(OMILL_QT_DOWNLOAD_TIMEOUT "20" CACHE STRING
  "Connection timeout (seconds) for aqt Qt downloads")

set(OMILL_LLVM_COMPONENTS
  Core
  IRReader
  IRPrinter
  BitReader
  BitWriter
  Linker
  Passes
  Analysis
  TransformUtils
  InstCombine
  ScalarOpts
  Support
  AggressiveInstCombine
  OrcJIT
  X86CodeGen
  X86AsmParser
  X86Info
  CACHE STRING "LLVM components to link against"
)
