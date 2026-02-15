# omill

An LLVM pass library for lowering [remill](https://github.com/lifting-bits/remill)-lifted IR to recompilable native code. Targets Windows x64 (PE) binaries using the Win64 ABI.

## Overview

omill transforms remill's semantics-preserving lifted IR — which operates on an explicit `State` struct and memory intrinsics — into clean, native LLVM IR suitable for recompilation. The pipeline progressively:

1. **Lowers remill intrinsics** (flags, memory, atomics, hyper calls) to native LLVM operations
2. **Optimizes State access** — dead store/flag elimination, promotes State fields to SSA, eliminates memory pointers
3. **Recovers control flow** — lowers `__remill_function_call`, `__remill_function_return`, `__remill_jump` to native branches/calls, then recovers the CFG
4. **Resolves dispatch targets** — folds program counters, resolves IAT calls, iteratively resolves indirect branches via constant folding
5. **Recovers ABI** — calling convention analysis, stack frame recovery, function signature recovery, State struct elimination
6. **Deobfuscation** (optional) — constant memory folding, stack data outlining, import hash resolution, lazy import resolution, dead path elimination

## Requirements

- **LLVM 21** (tested with prebuilt install at `C:/Program Files/LLVM21`)
- **CMake** >= 3.21
- **Ninja** (recommended generator)
- **C++17** compiler (Clang 21)

## Building

### Base build (no remill)

```bash
cmake -B build -G Ninja \
  -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" \
  -DOMILL_ENABLE_TOOLS=ON \
  -DOMILL_ENABLE_TESTING=ON

cmake --build build
```

### With remill (enables e2e tests)

First, build remill's dependencies:

```bash
cmake -G Ninja \
  -S third_party/remill/dependencies \
  -B third_party/remill/dependencies/build \
  -DUSE_EXTERNAL_LLVM=ON

cmake --build third_party/remill/dependencies/build
```

Then build omill with remill enabled:

```bash
cmake -B build-remill -G Ninja \
  -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" \
  -DOMILL_ENABLE_TOOLS=ON \
  -DOMILL_ENABLE_TESTING=ON \
  -DOMILL_ENABLE_REMILL=ON \
  -DCMAKE_PREFIX_PATH="$(pwd)/third_party/remill/dependencies/install"

cmake --build build-remill
```

### CMake options

| Option | Default | Description |
|--------|---------|-------------|
| `OMILL_ENABLE_TOOLS` | `ON` | Build `omill-opt` CLI tool |
| `OMILL_ENABLE_TESTING` | `ON` | Build unit and e2e tests |
| `OMILL_ENABLE_REMILL` | `OFF` | Build with remill for e2e testing |

## Usage

### As a library

```cpp
#include "omill/Omill.h"

llvm::ModulePassManager MPM;
omill::PipelineOptions opts;
opts.lower_intrinsics = true;
opts.optimize_state = true;
opts.lower_control_flow = true;
opts.recover_abi = true;
opts.resolve_indirect_targets = true;

omill::buildPipeline(MPM, opts);

llvm::ModuleAnalysisManager MAM;
llvm::FunctionAnalysisManager FAM;
// ... register standard + omill analyses ...
omill::registerAnalyses(FAM);
omill::registerModuleAnalyses(MAM);

MPM.run(*Module, MAM);
```

### omill-opt CLI

`omill-opt` is a standalone tool for running the pipeline on bitcode files:

```bash
omill-opt input.bc -o output.bc
```

## Architecture

### Pass pipeline

The pipeline is organized into stages that progressively lower remill IR:

| Stage | Passes | Purpose |
|-------|--------|---------|
| 1 | LowerFlagIntrinsics, RemoveBarriers, LowerMemoryIntrinsics, LowerAtomicIntrinsics, LowerHyperCalls | Replace remill intrinsics with native LLVM ops |
| 2 | DeadStateFlagElimination, DeadStateStoreElimination, PromoteStateToSSA, MemoryPointerElimination | Optimize away unnecessary State accesses |
| 3 | LowerErrorAndMissing, LowerFunctionReturn, LowerFunctionCall, LowerJump, CFGRecovery | Recover native control flow |
| 3.5 | FoldProgramCounter, ResolveIATCalls, LowerResolvedDispatchCalls | Resolve static dispatch targets |
| 3.6 | IterativeTargetResolution | Iteratively resolve indirect targets via optimization fixpoint |
| 4 | CallingConventionAnalysis, RecoverStackFrame, RecoverFunctionSignatures, EliminateStateStruct | Recover ABI and remove State |
| 5 | ConstantMemoryFolding, OutlineConstantStackData, HashImportAnnotation, ResolveLazyImports | Deobfuscation |
| 6 | LowerUndefinedIntrinsics | Final cleanup |

### Analyses

- **RemillIntrinsicAnalysis** — identifies and classifies remill intrinsic calls
- **StateFieldAccessAnalysis** — tracks which State struct fields are read/written
- **CallingConventionAnalysis** — determines calling conventions from register usage
- **BinaryMemoryMap** — provides constant memory contents from the original binary for folding

### Project structure

```
omill/
├── include/omill/          # Public headers
│   ├── Analysis/           # Analysis passes
│   ├── Passes/             # Transformation passes
│   └── Omill.h             # Pipeline builder API
├── lib/                    # Implementation
│   ├── Analysis/
│   ├── Passes/
│   └── Pipeline.cpp        # Pipeline construction
├── tools/
│   ├── omill-opt/          # Standalone optimizer tool
│   └── omill-lift/         # Lifter tool (requires remill)
├── tests/
│   ├── unit/               # Unit tests
│   └── e2e/                # End-to-end tests (require remill)
├── third_party/
│   └── remill/             # Remill submodule (binsnake fork)
└── cmake/
    └── options.cmake       # Build options
```

## Testing

```bash
# Run all tests
ctest --test-dir build

# Run unit tests only
ctest --test-dir build -R unit

# Run e2e tests (requires remill build)
ctest --test-dir build-remill -R e2e
```

## License

See [LICENSE](LICENSE) for details.
