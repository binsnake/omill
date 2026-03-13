#!/usr/bin/env python3
"""Summarize lifted IR shape metrics used by compact cleanup investigations."""

from __future__ import annotations

import argparse
import json
import pathlib
import re


PATTERNS = {
    "dispatch_call": re.compile(r"@__omill_dispatch_call\("),
    "dispatch_jump": re.compile(r"@__omill_dispatch_jump\("),
    "vm_entry": re.compile(r"vm_entry_"),
    "declare_blk": re.compile(r"^declare ptr @blk_", re.MULTILINE),
    "call_blk": re.compile(r"call ptr @blk_"),
    "musttail_blk": re.compile(r"musttail call ptr @blk_"),
    "define_native": re.compile(r"^define .*_native", re.MULTILINE),
    "call_native": re.compile(r"call .*_native"),
    "missing_block": re.compile(r"@__remill_missing_block\("),
    "missing_block_handler": re.compile(r"@__omill_missing_block_handler\("),
}


def summarize_ir(path: pathlib.Path) -> dict[str, int | str]:
    text = path.read_text(encoding="utf-8", errors="replace")
    metrics: dict[str, int | str] = {"path": str(path)}
    for name, pattern in PATTERNS.items():
        metrics[name] = len(pattern.findall(text))
    return metrics


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("paths", nargs="+", help="LLVM IR files to summarize")
    parser.add_argument(
        "--json",
        action="store_true",
        help="emit compact JSON lines instead of key=value text",
    )
    args = parser.parse_args()

    for raw_path in args.paths:
        path = pathlib.Path(raw_path)
        metrics = summarize_ir(path)
        if args.json:
            print(json.dumps(metrics, sort_keys=True))
            continue

        ordered_keys = ["path", *PATTERNS.keys()]
        parts = [f"{key}={metrics[key]}" for key in ordered_keys]
        print(" ".join(parts))

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
