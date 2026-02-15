option(OMILL_ENABLE_TESTING "Build omill tests" ON)
option(OMILL_ENABLE_TOOLS "Build omill-opt CLI tool" ON)
option(OMILL_ENABLE_REMILL "Build with remill for e2e testing" OFF)
option(OMILL_ENABLE_SIMPLIFIER "Build with EqSat MBA simplifier" OFF)

set(OMILL_LLVM_COMPONENTS
  Core
  IRReader
  IRPrinter
  BitReader
  BitWriter
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
