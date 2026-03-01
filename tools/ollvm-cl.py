"""ollvm-cl.py - Drop-in clang-cl wrapper with OLLVM obfuscation.

Three-step pipeline:  source -> IR -> ollvm-obf -> native .obj
Forwards all codegen flags to step 3 so ABI settings (/Gs, /GR-, /MT, etc.)
are preserved.  Preprocessor/language flags (/I, /D, /std:) are stripped for
step 3 since the IR is already preprocessed.
"""

import os
import sys
import subprocess
import tempfile

CLANG = r"C:\Program Files\LLVM21\bin\clang-cl.exe"
OLLVM = r"D:\binsnake\omill\build\tools\ollvm-obf\ollvm-obf.exe"
OLLVM_FLAGS = [
    "--substitute", "--opaque-predicates", "--bogus-control-flow", "--flatten",
    "--const-unfold", "--string-encrypt", "--bmi-mutate",
    "--if-convert", "--code-clone",
    "--schedule-instructions",
    "--arith-encode", "--stack-randomize",
    "--vectorize", "--vectorize-percent=5",
    "--internalize",
    "--dead-memory", "--opaque-addressing", "--entangle-arithmetic",
    "--opaque-constants", "--encode-literals", "--indirect-calls",
    "--cfi-poisoning", "--anti-symbolic", "--interproc-obf",
    "--skip-inline-asm", "--min-instructions=10", "--transform-percent=38",
    "--reg-pressure",
    "--verify-each",
]


def main() -> int:
    args = sys.argv[1:]

    # --- Parse out /Fo, /c, and source file ---
    outobj = None
    srcfile = None
    flags = []

    i = 0
    while i < len(args):
        a = args[i]

        # /FoPath or /Fo"Path"
        if a.upper().startswith("/FO"):
            outobj = a[3:]
            i += 1
            continue

        # /c — skip
        if a.upper() == "/C":
            i += 1
            continue

        # Source file detection
        lower = a.strip('"').lower()
        if lower.endswith((".cpp", ".cxx", ".cc")) and not lower.startswith("/"):
            srcfile = a
            i += 1
            continue

        flags.append(a)
        i += 1

    if not srcfile:
        print("[ollvm-cl] ERROR: no source file found in arguments", file=sys.stderr)
        return 1
    if not outobj:
        print("[ollvm-cl] ERROR: no /Fo found in arguments", file=sys.stderr)
        return 1

    # --- Build flag lists ---
    # IRARGS: everything (preprocessor + codegen) — needed for source -> IR
    irargs = list(flags)

    # CGARGS: strip preprocessor/language flags (IR is already preprocessed)
    # and optimisation-level flags (would undo obfuscation via InstCombine,
    # SimplifyCFG, GVN etc.).  We re-add -O2 with -disable-llvm-optzns so
    # codegen quality stays high without running IR optimisation passes.
    cgargs = []
    for f in flags:
        fu = f.upper().lstrip('"')
        if fu.startswith(("/I", "/D", "/STD:")):
            continue
        # /clang:-I... and /clang:-D...
        if fu.startswith("/CLANG:-I") or fu.startswith("/CLANG:-D"):
            continue
        # Strip optimisation levels — they re-run IR passes that undo obfuscation.
        if fu.startswith(("/O1", "/O2", "/OX")) or fu == "/OD":
            continue
        if fu.startswith("/CLANG:-O"):
            continue
        cgargs.append(f)

    # Good codegen (-O2) but skip IR-level optimisation passes that would
    # undo flattening, MBA substitution, opaque predicates, etc.
    cgargs.append("/clang:-O2")
    cgargs.append("/clang:-Xclang")
    cgargs.append("/clang:-disable-llvm-optzns")

    # Obfuscation inflates stack frames (flattening allocas, demote vars),
    # pushing past /Gs thresholds.  Force /GS- so the final .obj never
    # references __security_cookie (unavailable in kernel-mode drivers).
    cgargs.append("/GS-")

    tmpll = outobj + ".ollvm.ll"
    tmpobf = outobj + ".ollvm.obf.ll"

    try:
        # Step 1: source -> LLVM IR
        print("[ollvm-cl] Step 1/3: Compiling to IR...")
        cmd1 = [CLANG] + irargs + [
            "/clang:-S", "/clang:-emit-llvm",
            "/GS-",  # prevent sspstrong attrs in IR (kernel has no __security_cookie)
            f"/clang:-o", f"/clang:{tmpll}",
            srcfile,
        ]
        r = subprocess.run(cmd1)
        if r.returncode != 0:
            print("[ollvm-cl] ERROR: IR compilation failed", file=sys.stderr)
            return 1

        # Step 2: obfuscate
        print("[ollvm-cl] Step 2/3: Obfuscating...")
        cmd2 = [OLLVM] + OLLVM_FLAGS + [tmpll, "-o", tmpobf]
        r = subprocess.run(cmd2)
        if r.returncode != 0:
            print("[ollvm-cl] ERROR: obfuscation failed", file=sys.stderr)
            return 1

        # Step 3: obfuscated IR -> native .obj
        print("[ollvm-cl] Step 3/3: Compiling to native .obj...")
        cmd3 = [CLANG, "/c"] + cgargs + [tmpobf, f"/Fo{outobj}"]
        r = subprocess.run(cmd3)
        if r.returncode != 0:
            print("[ollvm-cl] ERROR: native compilation failed", file=sys.stderr)
            return 1

    finally:
        # Cleanup temp files
        for f in (tmpll, tmpobf):
            try:
                os.remove(f)
            except OSError:
                pass

    print(f"[ollvm-cl] Done: {outobj}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
