# OLLVM Obfuscation Workflow

End-to-end guide: from source code to obfuscated binary.

## The big picture

```
  Source code (.cpp)
       |
       v
  LLVM IR (.ll / .bc)          <-- clang-cl -emit-llvm
       |
       v
  ollvm-obf                    <-- 17 ordered transform passes
       |
       v
  Obfuscated IR (.ll / .bc)
       |
       v
  Native object (.obj)         <-- clang-cl -O2 -disable-llvm-optzns
       |
       v
  Linker (lld-link / link.exe)
       |
       v
  Final binary (.dll / .exe / .sys)
```

The critical constraint: the final compilation step (IR to `.obj`) must use
`-disable-llvm-optzns` to prevent LLVM's optimizer from undoing the
obfuscation transforms. `-O2` is still passed for codegen quality
(instruction selection, register allocation) but IR-level passes
(InstCombine, SimplifyCFG, GVN) are suppressed.

## Choosing a pipeline

| Question | LTO | Per-file |
|-|-|-|
| Do you need cross-TU analysis? | Yes | No |
| Do you use `--internalize` or `--interproc-obf`? | Required | Ineffective |
| Is build time a concern? | Longer (merge + single obf pass) | Parallel per-file |
| Can you modify the link step? | Must link the LTO `.obj` | Drop-in compiler swap |

**Use LTO** for maximum obfuscation strength. All translation units are
merged into a single module, giving the obfuscator full visibility for
internalization, interprocedural obfuscation, and dead code elimination.

**Use per-file** when LTO is impractical (very large projects, complex
build systems, or when you only want to obfuscate a few files).

## Workflow A: Whole-program LTO

### Step 0: Prerequisites

- LLVM 21 installed (`clang-cl`, `llvm-link`, `llvm-nm` on PATH or at known location)
- `ollvm-obf.exe` built (see `README.md`)
- Python 3.10+
- Project uses ClangCL toolset

### Step 1: Configure your vcxproj

Import the MSBuild targets and enable LTO for your release config:

```xml
<!-- After Microsoft.Cpp.targets -->
<Import Project="path\to\ollvm-msbuild.targets" />

<PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|x64'">
  <OllvmLtoEnabled>true</OllvmLtoEnabled>
</PropertyGroup>
```

Mark files that should not be obfuscated:

```xml
<ClCompile Include="vendor\zlib.cpp">
  <OllvmExclude>true</OllvmExclude>
</ClCompile>
```

### Step 2: Build

Build normally from Visual Studio or the command line. The normal compilation
runs first, then `OllvmLto` fires as a post-build step:

```
msbuild Project.vcxproj /p:Configuration=Release /p:Platform=x64
```

What happens behind the scenes:

```
[OLLVM] Starting whole-program LTO obfuscation...
[OLLVM] Step 1/4: Compiling 79 files to IR (8 jobs)...
[OLLVM] Step 2/4: Merging 79 IR files...
[OLLVM] Step 3/4: Obfuscating (18 passes, seed=0xB16B00B5)...
[OLLVM] Step 4/4: Compiling to native .obj...
[OLLVM] Obfuscation complete: x64\Release\Project_lto.obj
```

### Step 3: Link

The output is a single `.obj` containing all obfuscated code. Your linker
step needs to consume this object. For most projects, this means replacing
the intermediate `.obj` files with the single LTO object in your link
command or adjusting `<Link><AdditionalDependencies>`.

### Step 4: Verify

Run your test suite. Common issues at this stage:

- **Crash on startup**: A preserved symbol was missed. Add it to
  `OllvmLtoPreserve` or check your `.def` file.
- **Wrong results**: A pass introduced a bug (rare with `--verify-each`).
  Bisect by disabling passes one at a time.
- **Unresolved `__security_cookie`**: The pipeline adds `/GS-`
  automatically. Ensure nothing re-enables it.

## Workflow B: Per-file obfuscation

### Step 0: Configure paths

Edit `ollvm-cl.py`:

```python
CLANG = r"C:\Program Files\LLVM21\bin\clang-cl.exe"
OLLVM = r"D:\path\to\build\tools\ollvm-obf\ollvm-obf.exe"
```

### Step 1: Set the compiler

In your vcxproj:

```xml
<PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|x64'">
  <CLToolExe>ollvm-cl.cmd</CLToolExe>
  <CLToolPath>D:\path\to\omill\tools</CLToolPath>
</PropertyGroup>
```

### Step 2: Build and link normally

Each `.cpp` goes through the 3-step pipeline automatically. The output
`.obj` files are drop-in replacements for the originals.

## Workflow C: Standalone CLI

For one-off obfuscation of a single IR file:

```
:: Compile to IR
clang-cl /c /clang:-S /clang:-emit-llvm /GS- source.cpp /clang:-o source.ll

:: Obfuscate
ollvm-obf.exe --flatten --substitute --string-encrypt source.ll -o obfuscated.ll

:: Compile to native
clang-cl /c /clang:-O2 /clang:-Xclang /clang:-disable-llvm-optzns /GS- obfuscated.ll /Fo:source.obj
```

## Pass pipeline in detail

The passes execute in a fixed order. Each pass operates on the entire module,
transforming it in place. Understanding the order matters because earlier
passes create IR patterns that later passes must handle.

### Phase 1: Preparation

| Order | Pass | What it does |
|-|-|-|
| 1 | String encryption | Replaces string literal globals with encrypted data + decryption stubs. Must run first because later passes would break the decryption logic. |
| 2 | Code cloning | Duplicates internal functions with diversified arithmetic, creating 2-3 variants per function. Must run before per-function transforms so each clone is independently obfuscated. |

### Phase 2: Arithmetic-level transforms

| Order | Pass | What it does |
|-|-|-|
| 3 | Substitution | Replaces `add`, `sub`, `xor`, `and`, `or`, `shl`, `lshr`, `ashr` with equivalent MBA (Mixed Boolean-Arithmetic) expressions. Each operation becomes 3-7 instructions. |
| 4 | If-conversion | Converts simple diamond branches (`if/else`) to `select` instructions (cmov at machine level). Eliminates branch-based symbolic execution fork points. |
| 5 | Loop-to-recursion | Converts simple counted loops to tail-recursive functions. Opt-in only (`--loop-to-recursion`). |

### Phase 3: Control flow transforms

| Order | Pass | What it does |
|-|-|-|
| 6 | Flattening | Replaces structured control flow with a state-machine dispatch loop. All basic blocks become cases in a switch (or if-else tree). State transitions are affine-encoded. |
| 7 | Opaque predicates | Inserts always-true/false branches guarded by MBA zero-expressions or CRC32 intrinsic checks. The dead branch targets unreachable code but looks plausible. |
| 8 | Bogus control flow | Splits basic blocks and inserts dead code paths guarded by opaque predicates. Junk blocks contain realistic arithmetic referencing live values. |

### Phase 4: Instruction-level transforms

| Order | Pass | What it does |
|-|-|-|
| 9 | BMI mutation | Rewrites common bit operations using BMI1/BMI2 instruction patterns (`andn`, `blsi`, `blsmsk`, `bzhi`, `pdep`, `pext`). |
| 10 | Constant unfolding | Replaces integer constants with volatile-anchor-based expressions that evaluate to the same value at runtime but resist constant propagation. |

### Phase 5: Private passes (if built)

| Order | Pass | What it does |
|-|-|-|
| 11a | Internalize | Marks non-preserved functions as `internal`, enabling aggressive optimization by later passes. |
| 11b | Dead memory semantics | Inserts aliasing-opaque dead stores to confuse decompiler dead-store elimination. |
| 11c | Custom ABI | Shuffles parameters, injects bogus arguments, XORs return values of internal functions. |
| 11d | Opaque addressing | Routes stack variable access through volatile-indexed GEPs. |
| 11e | Entangle arithmetic | Injects opaque zeros (MBA expressions that equal 0) into arithmetic results. |
| 11f | Opaque constants | Replaces literal constants with multi-step ALU computation sequences. |
| 11g | Encode literals | XOR-encodes remaining constants via volatile-loaded keys. |
| 11h | Indirect calls | Replaces direct calls with image-base-relative indirect calls. |
| 11i | CFI poisoning | Injects phantom indirect call edges to pollute control flow graph recovery. |
| 11j | Anti-symbolic | Inserts state-explosion traps targeting symbolic execution engines. |
| 11k | Interprocedural obfuscation | Merges internal functions into dispatchers with call indirection. |

### Phase 6: Layout and scheduling

| Order | Pass | What it does |
|-|-|-|
| 12 | Instruction scheduling | Randomizes instruction order within basic blocks using Kahn's algorithm with randomized tie-breaking. |
| 13 | Function outlining | Extracts basic blocks into separate functions. Opt-in only (`--outline-functions`). |
| 14 | Arithmetic encoding | Applies affine transforms (`A*x + B`) on integer alloca values with modular inverse decode. |
| 15 | Stack randomization | Randomizes stack frame layout by inserting padding allocas and shuffling order. |

### Phase 7: Vectorization and finalization

| Order | Pass | What it does |
|-|-|-|
| 16 | Vectorize | Promotes scalar i32/i64 operations to SSE vector operations (`<4 x i32>` or `<2 x i64>`). Fills unused vector lanes with splitmix-derived noise. |
| 17 | Register pressure | Inserts identity inline asm constraints that extend register live ranges across basic blocks, forcing the register allocator to spill more. Must be last. |

### Final verification

After all passes, `llvm::verifyModule()` always runs regardless of
`--verify-each`. If verification fails, the tool exits with an error
message identifying the failing pass.

## Tuning obfuscation strength

### Controlling output size

The primary knob is `--transform-percent`. It controls the probability
(0-100) that any individual transform site is actually applied.

| `--transform-percent` | Typical bloat | Use case |
|-|-|-|
| 100 | 4-6x | Maximum protection. |
| 38 | 2-2.5x | Production default. Good balance. |
| 15 | 1.5-1.8x | Light obfuscation, fast builds. |

Other size-relevant flags:

| Flag | Effect on size | Notes |
|-|-|-|
| `--code-clone` | +30-60% | Creates 2-3 copies of each internal function. |
| `--vectorize-percent=N` | Proportional | Default 5. Higher = more scalar-to-vector promotion. |
| `--flatten` | +40-80% | Dispatch machinery per function. |
| `--stack-randomize` | +5-10% | Padding allocas. |

### Disabling expensive passes

For faster iteration during development, start with a minimal set:

```
--substitute --flatten --string-encrypt --verify-each
```

Then add passes incrementally to find the right balance for your project.

### Per-file granularity

Use `OllvmExclude` on files that:
- Contain vendor/third-party code (already obfuscated or too large)
- Have inline assembly incompatible with transforms
- Are hot paths where performance matters more than protection
- Contain boot/init code that must be minimal

### Per-function granularity (plugin mode)

With the pass plugin and `ollvm_attrs.h`:

```cpp
#include "ollvm_attrs.h"

OLLVM_ALL void secret_algorithm() { ... }        // Full obfuscation
OLLVM_NONE void performance_critical() { ... }    // No obfuscation
OLLVM_FLATTEN void state_machine() { ... }        // Only flatten
```

## Debugging obfuscation failures

### Bisecting a failing pass

If the obfuscated binary crashes, find which pass introduced the bug:

1. Start with all passes disabled.
2. Enable passes one at a time in pipeline order.
3. After each addition, rebuild and test.
4. The last pass added before failure is the culprit.

With `ollvm-lto.py`, use `--ollvm-flags` to control exactly which passes run:

```
python ollvm-lto.py --vcxproj=... --config=... --int-dir=... --out=... ^
  --ollvm-flags="--substitute --flatten --verify-each"
```

### Inspecting intermediate IR

Use `--keep-temps` with `ollvm-lto.py` to preserve intermediate files:

```
x64/Release/merged.ll            # Before obfuscation
x64/Release/merged.obf.ll        # After obfuscation
```

Compare the two to see exactly what changed. For per-file mode, the temp
files are `<output>.ollvm.ll` and `<output>.ollvm.obf.ll` (normally
cleaned up; comment out the cleanup in `ollvm-cl.py` to keep them).

### Verify-each

Always use `--verify-each` during development. It runs
`llvm::verifyModule()` after every pass and aborts immediately with the
name of the failing pass. Without it, a verifier error from pass 3 might
only manifest as a crash in pass 12, making diagnosis much harder.

### Common failure patterns

| Symptom | Likely cause | Fix |
|-|-|-|
| Verifier: "Use not dominated by def" | Flattening demoted a value incorrectly | File a bug with the IR that triggers it |
| Linker: unresolved `__security_cookie` | Missing `/GS-` | Ensure the flag is in both compile steps |
| Linker: unresolved `__chkstk` | Stack frame too large from padding | Reduce `--stack-randomize` or add `__chkstk` to preserve |
| Runtime: wrong computation result | MBA substitution or arithmetic encoding bug | Disable `--substitute` and `--arith-encode`, bisect |
| Runtime: infinite loop | Flattening state machine bug | Disable `--flatten`, report with minimal repro |
| Crash in obfuscated function | Opaque addressing or custom ABI broke a calling convention | Disable `--opaque-addressing` / `--custom-abi` |

## Seed determinism

All transforms are deterministic for a given seed. The base seed
(`--seed=N`, default `0xB16B00B5`) is mixed with a per-pass salt via
splitmix to produce independent sub-seeds. Same source + same seed +
same flags = identical output.

To get different obfuscation for each build (defense in depth):

```
--seed=%RANDOM%%RANDOM%
```

Or in MSBuild:

```xml
<OllvmLtoFlags>... --seed=$([System.DateTime]::Now.Ticks.ToString().Substring(10))</OllvmLtoFlags>
```

## Complete example: kernel project

```
:: 1. Build ollvm-obf
cd D:\binsnake\omill
cmake -B build -G Ninja -DLLVM_DIR="C:/Program Files/LLVM21/lib/cmake/llvm" -DOMILL_ENABLE_TOOLS=ON
cmake --build build --target ollvm-obf

:: 2. Run LTO pipeline on the hypervisor project
python tools\ollvm-lto.py ^
  --vcxproj=D:\project\Hypervisor.vcxproj ^
  --config="Release|x64" ^
  --int-dir=D:\project\x64\Release\ ^
  --out=D:\project\x64\Release\Hypervisor_lto.obj ^
  --jobs=8

:: 3. Link (using the project's existing link step, substituting the LTO obj)
lld-link /OUT:Hypervisor.dll ^
  D:\project\x64\Release\Hypervisor_lto.obj ^
  /DEF:Hypervisor.def ^
  /DLL /ENTRY:DriverEntry ...
```
