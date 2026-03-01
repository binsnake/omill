# MSBuild / Visual Studio Integration

This document covers integrating the OLLVM obfuscation pipeline into a
Visual Studio C++ project (`.vcxproj`).

## Overview

Two integration modes are available:

| Mode | Mechanism | Granularity | Cross-TU analysis |
|-|-|-|-|
| **Whole-program LTO** | `ollvm-msbuild.targets` | Per-file exclusion | Yes (all TUs merged) |
| **Per-file** | `ollvm-cl.cmd` as compiler | Per-file | No |

**LTO mode is recommended.** It merges all translation units before
obfuscation, enabling interprocedural passes (internalization, custom ABI,
call indirection) and whole-program constant propagation.

## LTO mode (recommended)

### 1. Import the targets file

Add this line near the bottom of your `.vcxproj`, **after** the
`Microsoft.Cpp.targets` import:

```xml
<Import Project="$(SolutionDir)..\omill\tools\ollvm-msbuild.targets" />
```

Adjust the path to point to your omill checkout.

### 2. Enable for your configuration

Add a `PropertyGroup` for the configuration you want to obfuscate:

```xml
<PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|x64'">
  <OllvmLtoEnabled>true</OllvmLtoEnabled>
</PropertyGroup>
```

### 3. Build normally

The obfuscation step runs automatically after the normal build completes.
Output appears in the MSBuild log prefixed with `[OLLVM]`.

### Properties reference

All properties have defaults. Override only what you need.

| Property | Default | Description |
|-|-|-|
| `OllvmLtoEnabled` | `false` | Master switch. Set to `true` to enable. |
| `OllvmLtoPython` | `python` | Python interpreter path. |
| `OllvmLtoScript` | Co-located `ollvm-lto.py` | Path to the LTO script. |
| `OllvmLtoPreserve` | Auto-detected from `.def` | Extra symbols to preserve (comma-separated). |
| `OllvmLtoJobs` | `$(NUMBER_OF_PROCESSORS)` | Parallel compilation jobs. |
| `OllvmLtoFlags` | Full default suite | Flags passed to `ollvm-obf`. See below. |
| `OllvmLtoOutput` | `$(IntDir)$(TargetName)_lto.obj` | Output `.obj` path. |

### Default OllvmLtoFlags

```
--substitute --opaque-predicates --bogus-control-flow --flatten
--const-unfold --string-encrypt --bmi-mutate --if-convert --code-clone
--schedule-instructions --arith-encode --stack-randomize
--vectorize --vectorize-percent=5 --internalize-all --internalize
--dead-memory --opaque-addressing --entangle-arithmetic --opaque-constants
--encode-literals --indirect-calls --cfi-poisoning --anti-symbolic
--interproc-obf --skip-inline-asm --min-instructions=10
--transform-percent=38 --reg-pressure --verify-each
```

Override to customize:

```xml
<PropertyGroup>
  <!-- Lighter obfuscation for faster builds -->
  <OllvmLtoFlags>--substitute --flatten --string-encrypt --verify-each</OllvmLtoFlags>
</PropertyGroup>
```

### Per-file exclusion

Mark individual source files to skip obfuscation. These files are still
compiled and included in the merged module (their symbols remain available
for cross-references), but all their functions receive an `ollvm_exclude`
attribute that every pass respects.

```xml
<ClCompile Include="vendor\iced_x86.cpp">
  <OllvmExclude>true</OllvmExclude>
</ClCompile>
```

Supports per-configuration conditions:

```xml
<ClCompile Include="core\entrypoint.cpp">
  <OllvmExclude Condition="'$(Configuration)'=='Debug'">true</OllvmExclude>
</ClCompile>
```

### Symbol preservation

Exported symbols are auto-detected from the project's `.def` file
(parsed from `<ModuleDefinitionFile>` in the vcxproj). The script runs
`llvm-nm` on the merged IR and cross-references against the `.def`
exports to build the `--preserve` list.

For additional symbols not in the `.def` (e.g., runtime callbacks):

```xml
<PropertyGroup>
  <OllvmLtoPreserve>DriverEntry,__chkstk,MyCallback</OllvmLtoPreserve>
</PropertyGroup>
```

### What the LTO pipeline does

When `OllvmLtoEnabled=true`, the `OllvmLto` target runs after the normal
build and executes `ollvm-lto.py`:

| Step | Input | Output | Description |
|-|-|-|-|
| 1 | `*.cpp` | `*.ll` | Parallel `clang-cl -emit-llvm` for each source file. Respects PCH, forced includes, per-file optimization overrides. |
| 2 | `*.ll` | `merged.ll` | `llvm-link` merges all translation units. |
| 3 | `merged.ll` | `obfuscated.ll` | `ollvm-obf` with the configured flags. |
| 4 | `obfuscated.ll` | `_lto.obj` | `clang-cl -O2 -disable-llvm-optzns` compiles to native. |

### Linking the output

The output `_lto.obj` is a single object file containing all obfuscated
code. To use it, your linker step should reference this object instead of
(or in addition to) the normal per-file `.obj` files.

For projects that already have a custom link step, point it at
`$(OllvmLtoOutput)`. For standard MSBuild linking, you may need to adjust
`<Link><AdditionalDependencies>` or replace the intermediate objects.

### Troubleshooting

**`__security_cookie` unresolved**: The pipeline adds `/GS-` automatically.
If you still see this, ensure your project doesn't force `/GS` after the
targets import.

**Step 1 fails on a file**: Check the `[OLLVM]` output for the failing
`clang-cl` command. Common issues: incompatible MSVC extensions, missing
include paths, PCH mismatches.

**Output is too large**: Reduce `--transform-percent` (default 38) or
disable expensive passes like `--code-clone`, `--vectorize`,
`--stack-randomize`. A typical bloat factor is 2-3x.

**Obfuscation undone by optimizer**: Verify step 4 uses
`-disable-llvm-optzns`. The scripts handle this automatically, but custom
`OllvmLtoFlags` that include optimization levels can conflict.

## Per-file mode (alternative)

For projects where LTO is not feasible, use `ollvm-cl.cmd` as a drop-in
compiler replacement.

### Setup

1. Edit `ollvm-cl.py` to set the correct paths:

```python
CLANG = r"C:\Program Files\LLVM21\bin\clang-cl.exe"
OLLVM = r"D:\binsnake\omill\build\tools\ollvm-obf\ollvm-obf.exe"
```

2. In your vcxproj, override the compiler for the desired configuration:

```xml
<PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|x64'">
  <CLToolExe>ollvm-cl.cmd</CLToolExe>
  <CLToolPath>D:\binsnake\omill\tools</CLToolPath>
</PropertyGroup>
```

3. Build normally. Each `.cpp` file goes through the 3-step pipeline
   (source to IR, obfuscate, IR to `.obj`).

### Limitations

- No cross-TU analysis (each file obfuscated independently).
- Private interprocedural passes (`--custom-abi`, `--interproc-obf`,
  `--internalize`) have limited effectiveness without whole-program view.
- Slower builds (3 subprocess invocations per source file).

## Toolset requirements

Both modes require the **ClangCL** toolset in Visual Studio.

### Selecting ClangCL in the vcxproj

```xml
<PropertyGroup Label="Configuration">
  <PlatformToolset>ClangCL</PlatformToolset>
  <!-- or LLVM_v143 for LLVM-specific toolset -->
</PropertyGroup>
```

Or in Visual Studio: Project Properties > General > Platform Toolset >
LLVM (clang-cl).

### Required tools on PATH

| Tool | Source | Used by |
|-|-|-|
| `clang-cl.exe` | LLVM 21 install | Compilation steps |
| `llvm-link.exe` | LLVM 21 install | LTO merge (step 2) |
| `llvm-nm.exe` | LLVM 21 install | Symbol preservation |
| `python.exe` | Python 3.10+ | Script execution |
| `ollvm-obf.exe` | omill build | Obfuscation (step 3) |

### Kernel / bare-metal projects

For projects targeting kernel mode or bare-metal environments:

- `/GS-` is applied automatically (no `__security_cookie` dependency).
- Ensure your project uses `/kernel` or equivalent restricted headers.
- The `--internalize` pass respects `.def` file exports, preserving
  your driver entry points.
- Excluded files (vendor code, arch-specific assembly wrappers) should
  use `<OllvmExclude>true</OllvmExclude>`.

## Example: complete vcxproj snippet

```xml
<?xml version="1.0" encoding="utf-8"?>
<Project DefaultTargets="Build" xmlns="http://schemas.microsoft.com/developer/msbuild/2003">

  <!-- ... standard project configuration ... -->

  <PropertyGroup Condition="'$(Configuration)|$(Platform)'=='Release|x64'">
    <PlatformToolset>ClangCL</PlatformToolset>
    <OllvmLtoEnabled>true</OllvmLtoEnabled>
    <OllvmLtoPreserve>DriverEntry</OllvmLtoPreserve>
  </PropertyGroup>

  <ItemGroup>
    <!-- Normal source files (obfuscated) -->
    <ClCompile Include="src\core.cpp" />
    <ClCompile Include="src\crypto.cpp" />

    <!-- Vendor code (excluded from obfuscation) -->
    <ClCompile Include="vendor\zlib.cpp">
      <OllvmExclude>true</OllvmExclude>
    </ClCompile>
  </ItemGroup>

  <!-- Standard MSVC targets -->
  <Import Project="$(VCTargetsPath)\Microsoft.Cpp.targets" />

  <!-- OLLVM LTO (must be after Microsoft.Cpp.targets) -->
  <Import Project="$(SolutionDir)..\omill\tools\ollvm-msbuild.targets" />

</Project>
```
