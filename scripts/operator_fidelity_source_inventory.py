#!/usr/bin/env python3
"""Supplementary exact-name inventory for the operator-fidelity semantic audit.

This report is deliberately lexical.  The failing Lean audit remains authoritative because this
script cannot distinguish declarations, proofs, comments, aliases, or projection-selected fields.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOTS = ("Mathlib", "Archive", "Counterexamples", "Wanted", "MathlibTest")
SELECTED = re.compile(
    r"(?<![A-Za-z0-9_])Rat\.(?:inv|div|zpow|divInt)(?![A-Za-z0-9_])"
    r"|(?<![A-Za-z0-9_.])mkRat(?![A-Za-z0-9_])"
)


def main() -> None:
    sys.stdout.reconfigure(encoding="utf-8")
    occurrences: list[tuple[str, int, str]] = []
    for source_root in SOURCE_ROOTS:
        for path in sorted((ROOT / source_root).rglob("*.lean")):
            for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
                if SELECTED.search(line):
                    occurrences.append((path.relative_to(ROOT).as_posix(), line_number, line.strip()))
    files = {path for path, _, _ in occurrences}
    print(f"occurrences={len(occurrences)} files={len(files)}")
    for path, line_number, line in occurrences:
        print(f"{path}:{line_number}:{line}")


if __name__ == "__main__":
    main()
