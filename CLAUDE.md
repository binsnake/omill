# omill - LLVM Lowering Library

## Build Commands
- **Standard Build (no remill):**
  `cmake -B build -G Ninja -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" -DOMILL_ENABLE_TOOLS=ON -DOMILL_ENABLE_TESTING=ON`
  `cmake --build build`
- **Build with Remill (enables e2e):**
  1. Dependencies: `cmake -G Ninja -S third_party/remill/dependencies -B third_party/remill/dependencies/build -DUSE_EXTERNAL_LLVM=ON && cmake --build third_party/remill/dependencies/build`
  2. Build omill: `cmake -B build-remill -G Ninja -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" -DOMILL_ENABLE_TOOLS=ON -DOMILL_ENABLE_TESTING=ON -DOMILL_ENABLE_REMILL=ON -DCMAKE_PREFIX_PATH="D:/binsnake/omill/third_party/remill/dependencies/install"`
  `cmake --build build-remill`

## Test Commands
- **Unit Tests:** `ctest --test-dir build -R unit`
- **E2E Tests:** `ctest --test-dir build-remill -R e2e`

## Coding Style
- **Standard:** C++17
- **Naming:** LLVM-style (UpperCamelCase types, lowerCamelCase functions/variables).
- **LLVM API:** Use explicit `llvm::` namespace prefixes (avoid `using namespace llvm;`).
- **Namespaces:** Wrap core logic in `namespace omill { ... }`.
- **Headers:** Use `#pragma once` and alphabetical include ordering.
- **Doxygen:** Use `///` for public API documentation.
- **Testing:** GoogleTest in `tests/unit`. Use `IRBuilder` for IR generation in tests.

## Tools
- `omill-opt`: Optimizer CLI for bitcode processing.
- `ollvm-obf`: Obfuscator for generating test inputs.
