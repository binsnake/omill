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
|-|-|-|
| `OMILL_ENABLE_TOOLS` | `ON` | Build `omill-opt` and `ollvm-obf` CLI tools |
| `OMILL_ENABLE_TESTING` | `ON` | Build unit and e2e tests |
| `OMILL_ENABLE_REMILL` | `OFF` | Build with remill for e2e testing |
| `OMILL_ENABLE_Z3` | auto | Z3-based dispatch solver (auto-downloads Z3 4.13.4) |
| `OMILL_ENABLE_SIMPLIFIER` | `OFF` | EqSat-based MBA simplification |

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
omill-opt input.bc -o output.bc --deobfuscate --resolve-targets --recover-abi
```

### ollvm-obf CLI

`ollvm-obf` applies OLLVM-style obfuscation to LLVM bitcode, useful for generating test inputs for the deobfuscation pipeline:

```bash
ollvm-obf input.bc -o output.bc --flatten --substitute --string-encrypt --const-unfold --vectorize
```

Supported transforms: control flow flattening, instruction substitution, string encryption, constant unfolding, and i32 vectorization (SSE2).

## Architecture

### Pass pipeline

The pipeline is organized into stages that progressively lower remill IR:

| Stage | Passes | Purpose |
|-|-|-|
| 0 | StripRemillIntrinsicBodies, AlwaysInlinerPass | Prepare lifted IR for processing |
| 1 | LowerRemillIntrinsics (Phase1: flags, barriers, memory, atomics, hyper calls) | Replace remill intrinsics with native LLVM ops |
| 2 | OptimizeState (DeadFlags, DeadStores, Promote), MemoryPointerElimination | Optimize away unnecessary State accesses |
| 3 | LowerRemillIntrinsics (Phase3: error/missing, return, call, jump), CFGRecovery | Recover native control flow |
| 3.5 | FoldProgramCounter, ResolveIATCalls, LowerRemillIntrinsics (ResolvedDispatch) | Resolve static dispatch targets |
| 3.6 | IterativeTargetResolution (ResolveAndLowerControlFlow + Z3DispatchSolver loop) | Iteratively resolve indirect targets via optimization fixpoint |
| 3.7 | InterProceduralConstProp | Propagate constants across call boundaries |
| 4 | CallingConventionAnalysis, RecoverStackFrame, RecoverStackFrameTypes, RecoverFunctionSignatures, RefineFunctionSignatures, RewriteLiftedCallsToNative, EliminateStateStruct | Recover ABI and remove State |
| 5 | SimplifyVectorReassembly, ConstantMemoryFolding, RecoverGlobalTypes, OutlineConstantStackData, HashImportAnnotation, ResolveLazyImports, EliminateDeadPaths | Deobfuscation |
| 6 | LowerRemillIntrinsics (Undefined) | Final cleanup |

### Consolidated passes

The pipeline uses 4 bitmask-configurable passes that each consolidate multiple related transformations, reducing IR traversal overhead:

- **LowerRemillIntrinsicsPass** — 11 intrinsic categories (flags, barriers, memory, atomics, hyper calls, error/missing, return, call, jump, undefined, resolved dispatch) selected via `LowerCategories` bitmask
- **OptimizeStatePass** — 5 state optimization phases (dead flags, dead stores, redundant bytes, promote-to-SSA, roundtrip elimination) selected via `OptimizePhases` bitmask
- **ResolveAndLowerControlFlowPass** — 3 resolution phases (constant-PC dispatch, jump table recovery, symbolic/SCEV solving) selected via `ResolvePhases` bitmask
- **SimplifyVectorReassemblyPass** — 4 XMM pattern matchers (constant vector folding, partial write collapse, byte reassembly coalescing, flag computation simplification)

### Analyses

- **RemillIntrinsicAnalysis** — identifies and classifies remill intrinsic calls
- **StateFieldAccessAnalysis** — tracks which State struct fields are read/written
- **CallGraphAnalysis** — builds inter-procedural call graph with SCC computation
- **CallingConventionAnalysis** — determines Win64 calling conventions from register usage (XMM0-3 param detection, callee-saved GPR filtering)
- **BinaryMemoryMap** — provides constant memory contents from the original binary for folding
- **LiftedFunctionMap** — maps program counter addresses to lifted `sub_<hex>` functions
- **ExceptionInfo** — recovers structured exception handling metadata

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
│   ├── omill-lift/         # Lifter tool (requires remill)
│   └── ollvm-obf/          # OLLVM-style obfuscation tool
├── tests/
│   ├── unit/               # Unit tests (266 tests)
│   └── e2e/                # End-to-end tests (require remill)
├── test_obf/               # Obfuscation round-trip test suite
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

## Credits

- [Dna](https://github.com/Colton1skees/Dna) — inspiration for remill-based recompilation by Colton1skees
- [remill](https://github.com/lifting-bits/remill) — binary lifter by Trail of Bits
- [LLVM](https://llvm.org/) — compiler infrastructure
- [Zydis](https://github.com/zyantific/zydis) — x86/x86-64 disassembler
- Inter-procedural analysis, type recovery, and string recovery passes co-authored with [Claude Code](https://claude.com/claude-code) (Anthropic)

## License

See [LICENSE](LICENSE) for details.
