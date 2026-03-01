"""ollvm-lto.py — Whole-program LTO obfuscation pipeline.

Compiles all project source files to LLVM bitcode, merges into a single
module via llvm-link, runs OLLVM obfuscation, then compiles to a single
native .obj ready for lld-link.

Usage:
    python ollvm-lto.py --vcxproj=path/to/project.vcxproj
                        --config=DebugOpt|x64
                        --int-dir=x64/DebugOpt
                        --out=x64/DebugOpt/Hypervisor_obf.obj
                        [--preserve=SYM,...]   # extra symbols (auto-detected from DEF)
                        [--jobs=N]
                        [--keep-temps]
                        [--no-obfuscate]       # merge only, skip ollvm-obf
                        [--ollvm-flags=...]     # override default OLLVM flags
"""

import argparse
import os
import sys
import subprocess
import xml.etree.ElementTree as ET
import concurrent.futures
import time
import shutil

# ── Tool paths ──────────────────────────────────────────────────────────
CLANG = r"C:\Program Files\LLVM21\bin\clang-cl.exe"
LLVM_LINK = r"C:\Program Files\LLVM21\bin\llvm-link.exe"
OLLVM = r"D:\binsnake\omill\build\tools\ollvm-obf\ollvm-obf.exe"
LLVM_NM = r"C:\Program Files\LLVM21\bin\llvm-nm.exe"

# Default OLLVM flags for whole-program obfuscation.
# --internalize-all is safe here because we have the entire program and
# --preserve protects true entry points / exports.
DEFAULT_OLLVM_FLAGS = [
    "--substitute", "--opaque-predicates", "--bogus-control-flow", "--flatten",
    "--const-unfold", "--string-encrypt", "--bmi-mutate",
    "--if-convert", "--code-clone",
    "--schedule-instructions",
    "--arith-encode", "--stack-randomize",
    "--vectorize", "--vectorize-percent=5",
    "--internalize-all", "--internalize",
    "--dead-memory", "--opaque-addressing", "--entangle-arithmetic",
    "--opaque-constants", "--encode-literals", "--indirect-calls",
    "--cfi-poisoning", "--anti-symbolic", "--interproc-obf",
    "--skip-inline-asm", "--min-instructions=10", "--transform-percent=38",
    "--reg-pressure",
    "--verify-each",
]

# XML namespace for MSBuild
NS = {"ms": "http://schemas.microsoft.com/developer/msbuild/2003"}


def parse_args():
    p = argparse.ArgumentParser(description="Whole-program LTO obfuscation")
    p.add_argument("--vcxproj", required=True, help="Path to .vcxproj file")
    p.add_argument("--config", required=True,
                   help="Configuration|Platform, e.g. DebugOpt|x64")
    p.add_argument("--int-dir", required=True,
                   help="Intermediate directory for .bc files")
    p.add_argument("--out", required=True,
                   help="Output .obj path")
    p.add_argument("--preserve", default="",
                   help="Extra comma-separated symbols to preserve (DEF exports auto-detected)")
    p.add_argument("--jobs", type=int, default=os.cpu_count() or 6,
                   help="Parallel compilation jobs")
    p.add_argument("--keep-temps", action="store_true",
                   help="Don't delete intermediate .bc/.ll files")
    p.add_argument("--no-obfuscate", action="store_true",
                   help="Merge only, skip obfuscation (for debugging)")
    p.add_argument("--ollvm-flags", default=None,
                   help="Override OLLVM flags (space-separated)")
    return p.parse_args()


def extract_sources(vcxproj_path, config_condition):
    """Parse the vcxproj and extract source files with per-file metadata.

    Returns a list of dicts:
        { "path": "relative/path.cpp",
          "forced_include": "some/pch.hpp" or None,
          "optimization": "Full" or None,
          "excluded": False,
          "pch_create": False,
          "ollvm_exclude": False }
    """
    tree = ET.parse(vcxproj_path)
    root = tree.getroot()
    sources = []

    for elem in root.iter(f"{{{NS['ms']}}}ClCompile"):
        inc = elem.get("Include")
        if not inc:
            continue

        # Check if file is excluded for this config
        excluded = False
        for ex in elem.findall("ms:ExcludedFromBuild", NS):
            cond = ex.get("Condition", "")
            if config_condition in cond and ex.text and ex.text.strip().lower() == "true":
                excluded = True

        # Get forced include for this config
        forced_include = None
        for fi in elem.findall("ms:ForcedIncludeFiles", NS):
            cond = fi.get("Condition", "")
            if config_condition in cond and fi.text:
                forced_include = fi.text.strip()
        # Also check PrecompiledHeaderFile for PCH groups (Use mode)
        if not forced_include:
            for pch in elem.findall("ms:PrecompiledHeader", NS):
                cond = pch.get("Condition", "")
                if config_condition in cond and pch.text == "Use":
                    for pchf in elem.findall("ms:PrecompiledHeaderFile", NS):
                        pchf_cond = pchf.get("Condition", "")
                        if config_condition in pchf_cond or not pchf_cond:
                            forced_include = pchf.text.strip() if pchf.text else None

        # Skip PCH-Create files (they just precompile the header, no code)
        is_pch_create = False
        for pch in elem.findall("ms:PrecompiledHeader", NS):
            cond = pch.get("Condition", "")
            if config_condition in cond and pch.text == "Create":
                is_pch_create = True

        # Get per-file optimization override
        opt = None
        for o in elem.findall("ms:Optimization", NS):
            cond = o.get("Condition", "")
            if config_condition in cond and o.text:
                opt = o.text.strip()

        # Check if file is excluded from OLLVM obfuscation
        ollvm_exclude = False
        for oe in elem.findall("ms:OllvmExclude", NS):
            cond = oe.get("Condition", "")
            if (not cond or config_condition in cond) and oe.text:
                if oe.text.strip().lower() == "true":
                    ollvm_exclude = True

        sources.append({
            "path": inc.replace("\\", "/"),
            "forced_include": forced_include.replace("\\", "/") if forced_include else None,
            "optimization": opt,
            "excluded": excluded,
            "pch_create": is_pch_create,
            "ollvm_exclude": ollvm_exclude,
        })

    return sources


def extract_compile_flags(vcxproj_path, config_condition):
    """Extract the ItemDefinitionGroup compile flags for the given config."""
    tree = ET.parse(vcxproj_path)
    root = tree.getroot()

    for idg in root.findall("ms:ItemDefinitionGroup", NS):
        cond = idg.get("Condition", "")
        if config_condition not in cond:
            continue

        cl = idg.find("ms:ClCompile", NS)
        if cl is None:
            continue

        flags = {}

        def text(tag):
            e = cl.find(f"ms:{tag}", NS)
            return e.text.strip() if e is not None and e.text else None

        flags["std"] = text("LanguageStandard") or "stdcpplatest"
        flags["optimization"] = text("Optimization") or "Disabled"
        flags["additional"] = text("AdditionalOptions") or ""
        flags["defines"] = text("PreprocessorDefinitions") or ""
        flags["undef"] = text("UndefinePreprocessorDefinitions") or ""
        flags["runtime_lib"] = text("RuntimeLibrary") or "MultiThreaded"
        flags["exception"] = text("ExceptionHandling") or "false"
        flags["buffer_check"] = text("BufferSecurityCheck") or "false"
        flags["cfg"] = text("ControlFlowGuard") or "false"
        flags["inline"] = text("InlineFunctionExpansion")
        flags["favor"] = text("FavorSizeOrSpeed")
        flags["omit_fp"] = text("OmitFramePointers")
        flags["intrinsics"] = text("IntrinsicFunctions")

        return flags

    return None


def extract_include_paths(vcxproj_path, config_condition):
    """Extract IncludePath for the given config."""
    tree = ET.parse(vcxproj_path)
    root = tree.getroot()

    for pg in root.findall("ms:PropertyGroup", NS):
        cond = pg.get("Condition", "")
        if config_condition not in cond:
            continue
        ip = pg.find("ms:IncludePath", NS)
        if ip is not None and ip.text:
            return ip.text.strip()
    return None



def extract_def_file(vcxproj_path, config_condition):
    """Extract ModuleDefinitionFile from the vcxproj Link settings."""
    tree = ET.parse(vcxproj_path)
    root = tree.getroot()

    for idg in root.findall("ms:ItemDefinitionGroup", NS):
        cond = idg.get("Condition", "")
        if config_condition not in cond:
            continue
        link = idg.find("ms:Link", NS)
        if link is None:
            continue
        mdf = link.find("ms:ModuleDefinitionFile", NS)
        if mdf is not None and mdf.text:
            return mdf.text.strip()
    return None


def parse_def_exports(def_path):
    """Parse a .def file and return all internal symbol names that must be preserved.

    For "exportname=internalname" lines, both names are included.
    For plain "exportname" lines, the name itself is included.
    """
    with open(def_path) as f:
        lines = f.readlines()

    symbols = set()
    in_exports = False
    for line in lines:
        line = line.strip()
        if line.upper() == "EXPORTS":
            in_exports = True
            continue
        if not in_exports or not line or line.startswith(";"):
            continue
        parts = line.split("=")
        export_name = parts[0].split()[0]
        internal_name = parts[1].strip() if len(parts) > 1 else export_name
        symbols.add(export_name)
        symbols.add(internal_name)
    return symbols


def resolve_preserve_from_def(def_path, merged_bc, extra_preserve):
    """Build --preserve patterns by cross-referencing DEF exports with bitcode symbols.

    Uses llvm-nm to find the actual (possibly mangled) names in the merged bitcode
    that correspond to DEF exports.  Always includes __exported_* and __chkstk globs.
    """
    def_syms = parse_def_exports(def_path)

    # Get all defined symbols from the merged bitcode
    r = subprocess.run([LLVM_NM, "--defined-only", merged_bc],
                       capture_output=True, text=True, timeout=30)
    bc_syms = set()
    for line in r.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 3:
            bc_syms.add(parts[2])

    # Match: exact DEF name, __exported_ prefixed, or contains DriverEntry/entry
    preserve = set()
    for sym in bc_syms:
        for ds in def_syms:
            if sym == ds or sym == f"__exported_{ds}":
                preserve.add(sym)
                break
        # Also preserve any symbol containing common entry point names
        if "DriverEntry" in sym:
            preserve.add(sym)

    # Glob patterns for safety
    preserve.add("__exported_*")
    preserve.add("__chkstk")

    # Merge with user-specified extra symbols
    if extra_preserve:
        for sym in extra_preserve.split(","):
            sym = sym.strip()
            if sym:
                preserve.add(sym)

    count = len(preserve)
    print(f"  Auto-detected {count} preserve patterns from {os.path.basename(def_path)}")
    return sorted(preserve)



def annotate_excluded_ll(ll_path):
    """Inject 'ollvm_exclude' attribute into all attribute groups of an .ll file.

    After this, every function in the file will carry the attribute, causing
    ollvm-obf PassFilter::shouldSkipFunction() to skip them.
    """
    import re
    with open(ll_path, 'r') as f:
        text = f.read()

    # Match 'attributes #N = { ... }' lines and inject the string attribute
    def inject(m):
        line = m.group(0)
        if '"ollvm_exclude"' in line:
            return line  # already present
        # Insert before closing '}'
        return line.rstrip().rstrip('}').rstrip() + ' "ollvm_exclude" }'

    text = re.sub(r'^attributes #\d+ = \{[^}]*\}',
                  inject, text, flags=re.MULTILINE)

    with open(ll_path, 'w') as f:
        f.write(text)


def build_common_args(flags, include_paths, project_dir):
    """Build the common clang-cl arguments from extracted flags."""
    args = []

    # Language standard — MSBuild uses 'stdcpplatest', clang-cl wants 'c++latest'
    std = flags['std']
    std_map = {"stdcpplatest": "c++latest", "stdcpp20": "c++20",
               "stdcpp17": "c++17", "stdcpp14": "c++14",
               "stdc17": "c17", "stdc11": "c11"}
    args.append(f"/std:{std_map.get(std, std)}")

    # Optimization
    opt_map = {"Disabled": "/Od", "MinSpace": "/O1", "MaxSpeed": "/O2",
               "Full": "/Ox"}
    args.append(opt_map.get(flags["optimization"], "/O2"))

    # Runtime library
    rt_map = {"MultiThreaded": "/MT", "MultiThreadedDLL": "/MD",
              "MultiThreadedDebug": "/MTd", "MultiThreadedDebugDLL": "/MDd"}
    args.append(rt_map.get(flags["runtime_lib"], "/MT"))

    # Security
    if flags["buffer_check"] == "false":
        args.append("/GS-")

    # Inline expansion
    il_map = {"Disabled": "/Ob0", "OnlyExplicitInline": "/Ob1",
              "AnySuitable": "/Ob2"}
    if flags["inline"] and flags["inline"] in il_map:
        args.append(il_map[flags["inline"]])

    # Frame pointers
    if flags.get("omit_fp") == "true":
        args.append("/Oy")

    # Intrinsics
    if flags.get("intrinsics") == "true":
        args.append("/Oi")

    # Favor
    favor_map = {"Speed": "/Ot", "Size": "/Os"}
    if flags.get("favor") and flags["favor"] in favor_map:
        args.append(favor_map[flags["favor"]])

    # Preprocessor defines
    if flags["defines"]:
        for d in flags["defines"].split(";"):
            d = d.strip()
            if d and d != "%(PreprocessorDefinitions)":
                args.append(f"/D{d}")

    # Undefines
    if flags["undef"]:
        for u in flags["undef"].split(";"):
            u = u.strip()
            if u:
                args.append(f"/U{u}")

    # Additional options (pass through verbatim)
    if flags["additional"]:
        for tok in flags["additional"].split():
            tok = tok.strip()
            if tok and tok != "%(AdditionalOptions)":
                args.append(tok)

    # Include paths — resolve MSBuild variables
    if include_paths:
        for p in include_paths.split(";"):
            p = p.strip()
            if not p:
                continue
            # Resolve common MSBuild variables
            p = p.replace("$(ProjectDir)", project_dir + "/")
            p = p.replace("$(SolutionDir)", project_dir + "/")
            # Skip remaining unresolved variables (VC_IncludePath etc.)
            if "$(" in p:
                continue
            full = os.path.normpath(p)
            if os.path.isdir(full):
                args.append(f"/I{full}")

    # Always add project dir as include (if not already present)
    proj_inc = f"/I{project_dir}"
    if proj_inc not in args:
        args.append(proj_inc)

    # Auto-detect vcpkg installed include paths
    for triplet in ["x64-windows-static", "x64-windows"]:
        vcpkg_inc = os.path.join(project_dir, "vcpkg_installed",
                                 triplet, triplet, "include")
        if os.path.isdir(vcpkg_inc):
            args.append(f"/I{vcpkg_inc}")
            break

    return args


def compile_to_bc(src_info, common_args, project_dir, int_dir):
    """Compile a single source file to LLVM bitcode (.bc).

    Returns (bc_path, success, stderr_text).
    """
    src_path = os.path.normpath(os.path.join(project_dir, src_info["path"]))
    # Output .ll in int_dir with flattened name
    bc_name = src_info["path"].replace("/", "_").replace("\\", "_")
    bc_name = os.path.splitext(bc_name)[0] + ".ll"
    bc_path = os.path.normpath(os.path.join(int_dir, bc_name))

    args = [CLANG, "/c"] + list(common_args)

    # Per-file optimization override
    if src_info["optimization"]:
        opt_map = {"Disabled": "/Od", "MinSpace": "/O1", "MaxSpeed": "/O2",
                   "Full": "/Ox"}
        override = opt_map.get(src_info["optimization"])
        if override:
            # Remove existing /O* and replace
            args = [a for a in args if not (a.startswith("/O") and
                    len(a) <= 3 and a[2:3] in "dsx12")]
            args.append(override)

    # Forced include (replaces PCH)
    if src_info["forced_include"]:
        fi_path = os.path.join(project_dir, src_info["forced_include"])
        args.append(f"/FI{fi_path}")

    # Emit LLVM text IR instead of native .obj.
    # Use /clang:-S /clang:-emit-llvm with /clang:-o (not /Fo) because
    # clang-cl's /Fo doesn't interact correctly with -emit-llvm.
    args.extend(["/clang:-S", "/clang:-emit-llvm",
                 f"/clang:-o", f"/clang:{bc_path}"])

    # Source file
    args.append(src_path)

    r = subprocess.run(args, capture_output=True, text=True, cwd=project_dir)
    return bc_path, r.returncode == 0, r.stderr


def main() -> int:
    args = parse_args()

    project_dir = os.path.dirname(os.path.abspath(args.vcxproj))
    config_condition = f"'$(Configuration)|$(Platform)'=='{args.config}'"

    # Parse vcxproj
    print(f"[ollvm-lto] Parsing {args.vcxproj} for {args.config}...")
    sources = extract_sources(args.vcxproj, config_condition)
    flags = extract_compile_flags(args.vcxproj, config_condition)
    include_paths = extract_include_paths(args.vcxproj, config_condition)
    def_file = extract_def_file(args.vcxproj, config_condition)
    if def_file and not os.path.isabs(def_file):
        def_file = os.path.join(project_dir, def_file)
    if def_file and os.path.isfile(def_file):
        print(f"  DEF file: {def_file}")
    else:
        def_file = None

    if not flags:
        print(f"[ollvm-lto] ERROR: No compile flags found for {args.config}",
              file=sys.stderr)
        return 1

    # Filter sources: remove build-excluded and PCH-create files
    sources = [s for s in sources if not s["excluded"] and not s["pch_create"]]

    # Identify OLLVM-excluded files (compiled to bitcode but not obfuscated)
    ollvm_excluded = {s["path"] for s in sources if s["ollvm_exclude"]}

    if ollvm_excluded:
        names = ', '.join(sorted(os.path.basename(p) for p in ollvm_excluded))
        print(f"[ollvm-lto] {len(ollvm_excluded)} files excluded from obfuscation: {names}")
    print(f"[ollvm-lto] {len(sources)} total, {len(sources) - len(ollvm_excluded)} to obfuscate")

    # Build common compile arguments
    common_args = build_common_args(flags, include_paths, project_dir)

    # Ensure intermediate directory exists
    bc_dir = os.path.join(project_dir, args.int_dir, "ollvm-lto")
    os.makedirs(bc_dir, exist_ok=True)

    # ── Step 1: Compile ALL sources to bitcode (parallel) ──────────────
    print(f"[ollvm-lto] Step 1/{4 if not args.no_obfuscate else 3}: "
          f"Compiling {len(sources)} files to bitcode ({args.jobs} jobs)...")
    t0 = time.time()

    bc_files = []
    excluded_bc_files = []  # .ll files from OllvmExclude'd sources
    failed = []

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futures = {}
        for src in sources:
            f = pool.submit(compile_to_bc, src, common_args, project_dir, bc_dir)
            futures[f] = src

        for f in concurrent.futures.as_completed(futures):
            src = futures[f]
            bc_path, ok, stderr = f.result()
            if ok:
                bc_files.append(bc_path)
                if src["path"] in ollvm_excluded:
                    excluded_bc_files.append(bc_path)
            else:
                failed.append(src["path"])
                # Print first error only
                if len(failed) <= 3:
                    print(f"  FAIL: {src['path']}", file=sys.stderr)
                    for line in stderr.strip().split("\n")[-5:]:
                        print(f"    {line}", file=sys.stderr)

    t1 = time.time()
    print(f"  {len(bc_files)} succeeded, {len(failed)} failed "
          f"({t1-t0:.1f}s)")

    if failed:
        if len(failed) > 3:
            print(f"  ... and {len(failed)-3} more failures", file=sys.stderr)
        print("[ollvm-lto] ERROR: Compilation failed", file=sys.stderr)
        return 1

    # Annotate excluded files' .ll with 'ollvm_exclude' function attribute
    if excluded_bc_files:
        print(f"  Annotating {len(excluded_bc_files)} excluded files with ollvm_exclude...")
        for ll in excluded_bc_files:
            annotate_excluded_ll(ll)

    # ── Step 2: Merge all bitcode ─────────────────────────────────────
    merged_bc = os.path.join(bc_dir, "merged.bc")
    print(f"[ollvm-lto] Step 2: Merging {len(bc_files)} bitcode files...")
    t0 = time.time()

    cmd = [LLVM_LINK] + bc_files + ["-o", merged_bc]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"[ollvm-lto] ERROR: llvm-link failed:\n{r.stderr}",
              file=sys.stderr)
        return 1

    merged_size = os.path.getsize(merged_bc) / 1024
    t1 = time.time()
    print(f"  Merged: {merged_size:.0f} KB ({t1-t0:.1f}s)")

    # ── Step 3: Obfuscate ─────────────────────────────────────────────
    obf_bc = os.path.join(bc_dir, "obfuscated.bc")

    if args.no_obfuscate:
        obf_bc = merged_bc
        print("[ollvm-lto] Skipping obfuscation (--no-obfuscate)")
    else:
        print("[ollvm-lto] Step 3: Obfuscating merged module...")
        t0 = time.time()

        ollvm_flags = (args.ollvm_flags.split() if args.ollvm_flags
                       else DEFAULT_OLLVM_FLAGS)

        # Auto-detect preserve symbols from DEF file exports
        if def_file:
            preserve_syms = resolve_preserve_from_def(
                def_file, merged_bc, args.preserve)
        else:
            # Fallback: user-specified + sensible defaults
            preserve_syms = ["__exported_*", "__chkstk", "*DriverEntry*"]
            if args.preserve:
                preserve_syms += [s.strip() for s in args.preserve.split(",")
                                  if s.strip()]

        preserve_flags = []
        for sym in preserve_syms:
            preserve_flags.extend(["--preserve", sym])

        cmd = [OLLVM] + ollvm_flags + preserve_flags + [merged_bc, "-o", obf_bc]
        r = subprocess.run(cmd, capture_output=True, text=True)
        if r.returncode != 0:
            print(f"[ollvm-lto] ERROR: ollvm-obf failed:\n{r.stderr}",
                  file=sys.stderr)
            return 1

        # Print ollvm-obf's diagnostic output
        for line in r.stderr.strip().split("\n"):
            if line.strip():
                print(f"  {line}")

        obf_size = os.path.getsize(obf_bc) / 1024
        t1 = time.time()
        print(f"  Obfuscated: {obf_size:.0f} KB ({t1-t0:.1f}s)")

    # ── Step 4: Compile to native .obj ────────────────────────────────
    out_obj = os.path.join(project_dir, args.out)
    step_n = 3 if args.no_obfuscate else 4
    print(f"[ollvm-lto] Step {step_n}: Compiling to native .obj...")
    t0 = time.time()

    # Build codegen flags: strip preprocessor/language flags (already in IR),
    # strip optimization-level flags (would undo obfuscation).
    # Keep codegen flags: /GS-, /GR-, target arch, etc.
    cg_args = [CLANG, "/c"]

    for a in common_args:
        au = a.upper()
        # Skip preprocessor/language flags
        if au.startswith(("/D", "/U", "/I", "/STD:", "/FI")):
            continue
        # Skip optimization levels
        if au.startswith(("/O1", "/O2", "/OX")) or au == "/OD":
            continue
        if au.startswith("/CLANG:-O"):
            continue
        if au.startswith("/CLANG:-D") or au.startswith("/CLANG:-I"):
            continue
        cg_args.append(a)

    # Good codegen but skip IR-level optimization passes
    cg_args.extend(["/clang:-O2", "/clang:-Xclang", "/clang:-disable-llvm-optzns"])
    # Prevent __security_cookie references
    cg_args.append("/GS-")

    cg_args.extend([obf_bc, f"/Fo{out_obj}"])

    os.makedirs(os.path.dirname(out_obj), exist_ok=True)
    r = subprocess.run(cg_args, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"[ollvm-lto] ERROR: Native compilation failed:\n{r.stderr}",
              file=sys.stderr)
        return 1

    obj_size = os.path.getsize(out_obj) / 1024
    t1 = time.time()
    print(f"  Output: {out_obj} ({obj_size:.0f} KB, {t1-t0:.1f}s)")

    # ── Cleanup ───────────────────────────────────────────────────────
    if not args.keep_temps:
        shutil.rmtree(bc_dir, ignore_errors=True)

    print(f"[ollvm-lto] Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
