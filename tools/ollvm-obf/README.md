# OLLVM Obfuscation Toolchain

Whole-program and per-file LLVM IR obfuscation for Windows x64 targets.
Supports ClangCL, MSBuild, and standalone CLI usage.

## Prerequisites

| Dependency | Version | Notes |
|-|-|-|
| LLVM | 21 | Install to `C:\Program Files\LLVM21`. Needs `clang-cl.exe`, `llvm-link.exe`, `llvm-nm.exe`. |
| Python | 3.10+ | Required by `ollvm-cl.py` and `ollvm-lto.py`. |
| CMake | 3.21+ | Build system. |
| Ninja | any | Recommended generator. |

## Standalone use (outside omill)

The obfuscation toolchain has **zero dependencies on the omill core**.
`ollvm-obf` and `ollvm-plugin` link only against LLVM and include only
their own sibling headers. They can be extracted into a standalone project.

### What to copy

```
my-ollvm/
  ollvm-obf/          # All .cpp and .h files from tools/ollvm-obf/
    private/           # Optional: your private passes
  ollvm-plugin/        # OllvmPlugin.cpp, ollvm_attrs.h
  ollvm-cl.py          # Per-file wrapper script
  ollvm-cl.cmd         # CMD shim for MSBuild
  ollvm-lto.py         # Whole-program LTO script
  ollvm-msbuild.targets
  CMakeLists.txt       # Use standalone-CMakeLists.txt as starting point
```

A ready-made `standalone-CMakeLists.txt` is provided. Rename it to
`CMakeLists.txt` and adjust paths to match your directory layout.

### Building standalone

```
cmake -B build -G Ninja -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm"
cmake --build build
```

### What you get

| Artifact | Description |
|-|-|
| `ollvm-obf.exe` | Standalone IR obfuscation tool. |
| `OllvmPlugin.dll` | LLVM pass plugin for per-function annotation. |

### Path fixups

After extraction, update the hardcoded paths in:

- `ollvm-cl.py` lines 14-15: `CLANG` and `OLLVM`
- `ollvm-lto.py` lines 29-32: `CLANG`, `LLVM_LINK`, `OLLVM`, `LLVM_NM`


## Building ollvm-obf

### Minimal (obfuscation tool only)

```
cmake -B build -G Ninja ^
  -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" ^
  -DOMILL_ENABLE_TOOLS=ON ^
  -DOMILL_ENABLE_TESTING=OFF

cmake --build build --target ollvm-obf
```

Output: `build/tools/ollvm-obf/ollvm-obf.exe`

### With tests

```
cmake -B build -G Ninja ^
  -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" ^
  -DOMILL_ENABLE_TOOLS=ON ^
  -DOMILL_ENABLE_TESTING=ON

cmake --build build --target ollvm-obf omill-ollvm-obf-unit-tests omill-ollvm-jit-tests
```

Test binaries:

| Target | What it tests |
|-|-|
| `omill-ollvm-obf-unit-tests` | Per-pass unit tests (GoogleTest). |
| `omill-ollvm-jit-tests` | Compile C++ to IR, obfuscate, JIT execute, verify results. |

### CMake options

| Option | Default | Description |
|-|-|-|
| `OMILL_ENABLE_TOOLS` | ON | Build `ollvm-obf`, `omill-opt`, plugin. |
| `OMILL_ENABLE_TESTING` | ON | Build test targets. |
| `OMILL_ENABLE_REMILL` | OFF | Enable remill-based e2e deobfuscation tests. |
| `OMILL_ENABLE_Z3` | OFF | Z3 constraint solver for dispatch resolution. |
| `OMILL_ENABLE_SIMPLIFIER` | OFF | Rust EqSat MBA simplifier. |

## Private passes

Non-redistributable passes live in `tools/ollvm-obf/private/`, which is
git-ignored. The build system detects their presence automatically.

### Directory structure

```
tools/ollvm-obf/private/
  PrivatePasses.h          # Required facade header
  PrivatePasses.cpp        # Required: implements ollvm::priv::runPasses()
  AntiSymbolic.cpp         # Individual pass implementations
  CFIPoisoning.cpp
  CustomABI.cpp
  DeadMemorySemantics.cpp
  EncodeLiterals.cpp
  EntangleArithmetic.cpp
  IndirectCalls.cpp
  InternalizeModule.cpp
  InterproceduralObfuscation.cpp
  OpaqueAddressing.cpp
  OpaqueConstants.cpp
```

### How it works

1. CMake checks `IS_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/private"` at
   configure time.
2. If the directory exists and contains `.cpp` files, they are globbed into
   the `ollvm-obf` target and `OLLVM_HAS_PRIVATE` is defined.
3. `main.cpp` conditionally includes `PrivatePasses.h` and calls
   `ollvm::priv::runPasses(M, seed, filter)` after the public passes.

### Facade contract

`PrivatePasses.h` must expose:

```cpp
#pragma once
#include "../PassFilter.h"
namespace llvm { class Module; }

namespace ollvm::priv {
void runPasses(llvm::Module &M, uint64_t base_seed, const FilterConfig &filter);
}
```

### Adding a new private pass

1. Create `private/MyPass.h` and `private/MyPass.cpp`.
2. Add a `cl::opt<bool>` flag in `PrivatePasses.cpp`.
3. Call your pass from `runPasses()`.
4. Re-run `cmake -B build` (file glob requires reconfigure).

### Verifying the build

```
cmake --build build --target ollvm-obf
```

With private passes:
```
[cmake] ollvm-obf: private passes enabled
```

Without:
```
(no message, compiles only public passes)
```

## Usage modes

### 1. Standalone CLI

```
ollvm-obf.exe [flags] input.ll -o output.ll
ollvm-obf.exe [flags] input.bc -o output.bc
```

Output format is determined by extension: `.ll` for text IR, `.bc` for bitcode.

### 2. Per-file wrapper (ollvm-cl)

`ollvm-cl.py` is a drop-in `clang-cl.exe` replacement. It runs a 3-step
pipeline:

| Step | Command | Purpose |
|-|-|-|
| 1 | `clang-cl <all flags> /clang:-S /clang:-emit-llvm /GS-` | Source to LLVM IR. |
| 2 | `ollvm-obf <OLLVM_FLAGS> input.ll -o output.ll` | Obfuscate IR. |
| 3 | `clang-cl /c <codegen flags> /clang:-O2 /clang:-disable-llvm-optzns /GS-` | IR to native `.obj`. |

Step 3 strips preprocessor (`/I`, `/D`, `/std:`) and optimization (`/O1`,
`/O2`, `/Ox`) flags to prevent LLVM's optimizer from undoing obfuscation.
It re-adds `/clang:-O2 /clang:-disable-llvm-optzns` for good codegen
quality without IR-level optimization passes.

**Setup:** Edit the paths at the top of `ollvm-cl.py`:

```python
CLANG = r"C:\Program Files\LLVM21\bin\clang-cl.exe"
OLLVM = r"D:\binsnake\omill\build\tools\ollvm-obf\ollvm-obf.exe"
```

A thin `ollvm-cl.cmd` shim exists to call the Python script from MSBuild
or batch contexts.

### 3. Whole-program LTO (ollvm-lto)

`ollvm-lto.py` parses a `.vcxproj` file and runs a 4-step whole-program
obfuscation pipeline:

| Step | What happens |
|-|-|
| 1 | Compile all sources to `.ll` in parallel (respects PCH, forced includes, per-file flags). |
| 2 | Merge all `.ll` files via `llvm-link`. |
| 3 | Run `ollvm-obf` on the merged module. Auto-detects exports from `.def` file. |
| 4 | Compile obfuscated `.ll` to a single `.obj`. |

```
python ollvm-lto.py ^
  --vcxproj=path/to/Project.vcxproj ^
  --config="DebugOpt|x64" ^
  --int-dir=x64/DebugOpt/ ^
  --out=x64/DebugOpt/project_lto.obj ^
  --jobs=8 ^
  --ollvm-flags="--substitute --flatten ..."
```

#### Per-file exclusion

Mark files in your `.vcxproj` with `<OllvmExclude>`:

```xml
<ClCompile Include="vendor\iced_x86.cpp">
  <OllvmExclude>true</OllvmExclude>
</ClCompile>
```

Excluded files are still compiled and linked into the merged module (for
cross-references), but all their functions receive an `ollvm_exclude`
attribute that `PassFilter` skips.

### 4. Pass plugin (OllvmPlugin.dll)

For per-function annotation-based obfuscation during normal compilation.
Requires LLVM built with `LLVM_EXPORT_SYMBOLS_FOR_PLUGINS=ON` (not the
case with stock LLVM releases on Windows).

```
set OLLVM_DEFAULTS=flatten,substitute,opaque-predicates
set OLLVM_SEED=42
clang-cl -fpass-plugin=OllvmPlugin.dll /O2 source.cpp
```

Per-function control via `ollvm_attrs.h`:

```cpp
#include "ollvm_attrs.h"

OLLVM_ALL void critical_function() { ... }
OLLVM_NONE void fast_path() { ... }
OLLVM_FLATTEN OLLVM_INDIRECT_CALLS int dispatch(int x) { ... }
```

## CLI flags reference

### Public passes

| Flag | Description |
|-|-|
| `--substitute` | MBA instruction substitution (add, sub, xor, and, or, shifts). |
| `--opaque-predicates` | Insert always-true/false MBA and CRC32 predicates. |
| `--bogus-control-flow` | Insert dead code paths guarded by opaque predicates. |
| `--flatten` | Control flow flattening with affine-encoded dispatch. |
| `--const-unfold` | Replace constants with volatile-anchor-based expressions. |
| `--string-encrypt` | Rolling feedback cipher on string literals. |
| `--bmi-mutate` | Rewrite with BMI1/BMI2 bit-manipulation instructions. |
| `--schedule-instructions` | Randomize instruction order within basic blocks. |
| `--if-convert` | Convert diamond branches to `select` (cmov). |
| `--outline-functions` | Outline basic blocks into separate functions. Opt-in. |
| `--stack-randomize` | Randomize stack frame layout with padding and shuffle. |
| `--arith-encode` | Affine transforms on integer allocas. |
| `--loop-to-recursion` | Convert simple loops to tail-recursive functions. Opt-in. |
| `--code-clone` | Clone internal functions with diversified arithmetic. |
| `--reg-pressure` | Extend register live ranges via inline asm anchors. Must be last. |
| `--vectorize` | Replace scalar i32/i64 ops with SSE vector operations. |

### Vectorize sub-flags

| Flag | Default | Description |
|-|-|-|
| `--vectorize-data` | true | Vectorized stack data mutation. |
| `--vectorize-bitwise` | false | Bitwise decomposition for vectorized add/sub. |
| `--vectorize-i64` | true | Also vectorize i64 using `<2 x i64>`. |
| `--vectorize-percent=N` | 40 | Percent of eligible operations to vectorize. |

### Private passes (require `private/` build)

| Flag | Description |
|-|-|
| `--internalize` | Mark non-preserved functions/globals as internal. |
| `--internalize-all` | Also internalize `dso_local` symbols. |
| `--preserve=PAT` | Symbol glob patterns to keep external (repeatable). |
| `--custom-abi` | Shuffle parameters, inject bogus args, XOR returns. |
| `--interproc-obf` | Merge internal functions into dispatchers + call indirection. |
| `--encode-literals` | XOR-encode constants via volatile-loaded key. |
| `--entangle-arithmetic` | Inject opaque zeros into arithmetic results. |
| `--indirect-calls` | Replace direct calls with image-base-split indirect calls. |
| `--opaque-addressing` | Route alloca access through volatile-indexed GEPs. |
| `--opaque-constants` | Replace literal constants with multi-step ALU sequences. |
| `--cfi-poisoning` | Inject phantom indirect call edges to pollute CFG recovery. |
| `--anti-symbolic` | Insert state-explosion traps for symbolic execution. |
| `--dead-memory` | Insert aliasing-opaque dead stores to confuse DSE. |

### Global controls

| Flag | Default | Description |
|-|-|-|
| `--seed=N` | 0xB16B00B5 | Base RNG seed. Deterministic output for same seed. |
| `--verify-each` | false | Run LLVM verifier after each pass. Recommended. |
| `--min-instructions=N` | 0 | Skip functions with fewer than N instructions. |
| `--transform-percent=N` | 100 | Per-site transform probability (0-100). |
| `--skip-inline-asm` | false | Skip functions containing inline assembly. |

### Recommended production defaults

```
--substitute --opaque-predicates --bogus-control-flow --flatten
--const-unfold --string-encrypt --bmi-mutate --if-convert --code-clone
--schedule-instructions --arith-encode --stack-randomize
--vectorize --vectorize-percent=5
--skip-inline-asm --min-instructions=10 --transform-percent=38
--reg-pressure --verify-each
```

With private passes, add:

```
--internalize --dead-memory --opaque-addressing --entangle-arithmetic
--opaque-constants --encode-literals --indirect-calls --cfi-poisoning
--anti-symbolic --interproc-obf
```

### Pass execution order

Passes execute in a fixed order regardless of flag order on the command line:

1. String encryption
2. Code cloning
3. Substitution
4. If-conversion
5. Loop-to-recursion
6. Flattening
7. Opaque predicates
8. Bogus control flow
9. BMI mutation
10. Constant unfolding
11. *Private passes (if built)*
12. Instruction scheduling
13. Function outlining
14. Arithmetic encoding
15. Stack randomization
16. Vectorize
17. Register pressure (must be last)
