# Archive

`Archive/` preserves self-contained formalizations of particular results,
problems, computations, classifications, and distinctive alternative proofs.
Put generally useful definitions, constructions, and lemmas in their subject
modules in `Mathlib/`. Results that naturally extend a mathematical theory can
belong in `Mathlib/` before they have downstream users. Archived material can
move into `Mathlib/` when it passes the review for a canonical interface.
[Mathematical scope and placement](../FORK_DESIGN.md#mathematical-scope-and-placement)

Both locations apply the same requirements for mathematical fidelity, proof
status, axiom and evaluation trust, provenance, and licensing. An Archive
development may use problem-specific statements, local names, and local
interfaces. Follow the repository's shared style and documentation conventions.

`Archive` modules may import `Mathlib`. Keep `Mathlib` free of direct and
transitive dependencies on `Archive`.

## Contributing

Submit a pull request to this fork's `main` branch. Describe the result,
explain its proposed placement and any reusable prerequisites, and include
the mathematical, source, and verification evidence required by the
[contribution guide](../.github/CONTRIBUTING.md).
