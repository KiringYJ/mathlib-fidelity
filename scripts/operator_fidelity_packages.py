#!/usr/bin/env python3
"""Run ownership-scoped operator audits on the built companion packages."""

from __future__ import annotations

import argparse
from pathlib import Path
import subprocess


ROOT = Path(__file__).resolve().parents[1]
TEST_PACKAGES = ("MathlibTest", "FidelityTest")
PACKAGES = ("Archive", "Counterexamples", "Wanted", *TEST_PACKAGES)
TEST_EXCLUSIONS = {
    # Deliberate retired operations checked by the linter's negative regression fixture.
    "FidelityTest.Linter.OperatorFidelity",
    # The command-only Mathlib audit is already run by the test target.
    "FidelityTest.Linter.OperatorFidelityFull",
}


def run_audit(package: str, modules: list[str], output_dir: Path, label: str) -> bool:
    source = output_dir / f"{label}.lean"
    log = output_dir / f"{label}.log"
    # Legacy imports load private definitions throughout the imported module graph.
    imports = [f"import {module}" for module in modules]
    source.write_text("\n".join([
        *imports,
        "import Mathlib.Tactic.Linter.OperatorFidelity",
        "",
        "set_option maxHeartbeats 0",
        f"#operator_fidelity with_proofs in {package}",
        "",
    ]), encoding="utf-8")

    with log.open("wb") as stream:
        result = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT,
                                stdout=stream, stderr=subprocess.STDOUT, check=False)
    print(f"{label}: {len(modules)} imports, exit {result.returncode}. {log}", flush=True)
    if result.returncode == 0:
        return True

    # Independent test fixtures can define the same global name. Only split on import collisions.
    if package in TEST_PACKAGES and len(modules) > 1:
        with log.open(encoding="utf-8", errors="replace") as stream:
            collision = any("failed, environment already contains" in line for line in stream)
        if collision:
            middle = len(modules) // 2
            left = run_audit(package, modules[:middle], output_dir, f"{label}-1")
            right = run_audit(package, modules[middle:], output_dir, f"{label}-2")
            return left and right
    return False


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("packages", nargs="*", metavar="PACKAGE",
                        help=f"Audit {', '.join(PACKAGES)}. Default is every package.")
    args = parser.parse_args()
    for package in args.packages:
        if package not in PACKAGES:
            parser.error(f"unknown package: {package}")
    output_dir = ROOT / ".lake" / "operator-fidelity-packages"
    output_dir.mkdir(parents=True, exist_ok=True)

    success = True
    for package in args.packages or PACKAGES:
        modules = [package]
        if package in TEST_PACKAGES:
            modules = [
                ".".join(path.relative_to(ROOT).with_suffix("").parts)
                for path in sorted((ROOT / package).rglob("*.lean"))
            ]
            modules = [module for module in modules if module not in TEST_EXCLUSIONS]
            if not modules:
                raise SystemExit(f"No {package} source modules found.")
        success = run_audit(package, modules, output_dir, package) and success
    return int(not success)


if __name__ == "__main__":
    raise SystemExit(main())
