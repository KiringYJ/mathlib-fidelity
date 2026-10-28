#!/usr/bin/env python3
"""Reject unreviewed GitHub workflows after upstream reconciliation."""

from pathlib import Path
import sys


WORKFLOWS = frozenset(
    {
        "actionlint.yml",
        "cache_test.yml",
        "fidelity-ci.yml",
        "fidelity-proof-check.yml",
        "pre-commit.yml",
    }
)


def check_workflows(repository: Path) -> list[str]:
    """Check the active workflow inventory; archived workflows are inert."""
    directory = repository / ".github" / "workflows"
    active = {
        path.name
        for path in directory.iterdir()
        if path.is_file() and path.suffix.lower() in {".yml", ".yaml"}
    }
    errors = [f"Unreviewed active workflow: {name}" for name in sorted(active - WORKFLOWS)]
    errors += [f"Missing required workflow: {name}" for name in sorted(WORKFLOWS - active)]
    return errors


def main() -> int:
    errors = check_workflows(Path(__file__).resolve().parents[1])
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        print("Review .github/CI.md before publishing workflow changes.", file=sys.stderr)
    return int(bool(errors))


if __name__ == "__main__":
    sys.exit(main())
