# mathlib-fidelity

`mathlib-fidelity` is a maintainer-curated downstream distribution of
[mathlib](https://github.com/leanprover-community/mathlib4). It retains
mathlib's implementation and theorem base while developing an independent,
mathematician-facing library whose public API prioritizes mathematical fidelity
and quality of life.

External contributions to this fork are welcome through pull requests that
target `main` and follow the repository policy. Fork-only changes are developed
for this distribution and are not prepared for submission to upstream.
Upstream remains a source of sound implementation, theorems, and updates, but
it is not the design authority for this fork.

## Design priorities

- Formalize useful relationships between mathematical theories through
  explicit constructions, maps, equivalences, and laws governing their composition.
  [Interoperability between mathematical theories](FORK_DESIGN.md#interoperability-between-mathematical-theories)
- Require context or explicit input to determine mathematical types,
  operations, and structures. Use priorities to order coherent searches.
  [Priority-independent mathematical semantics](FORK_DESIGN.md#priority-independent-mathematical-semantics)
- Represent genuinely partial mathematical operations with explicit domains or
  explicit partiality rather than silent fallback values.
- Retain official Lean and legitimate core types such as `Rat`. Exclude
  unfaithful operators from mathematical definitions and statements, remove
  replaceable proof uses, and document unavoidable toolchain proof dependencies.
- Prefer established mathematical vocabulary and discoverable public APIs over
  representation-driven interfaces.
- Treat natural formal proofs and real downstream formalizations as tests of
  API quality.
- Complete each accepted migration across its selected API and all affected
  consumers in one delivery, without compatibility or transitional layers.
  Track independent foundational problems in separate issues when a proved boundary
  preserves the completed API's mathematical contract.
- Admit external formalizations through explicit mathematical, licensing,
  provenance, and implementation review.

See the [design charter](FORK_DESIGN.md) for the criteria that govern API and
migration decisions. The [changelog](CHANGELOG.md) records delivered changes.

## Branch model

- `main` is the canonical personal branch, GitHub default branch, and daily
  driver. Its published history includes Fidelity changes and the reconciled
  mathlib releases.
- `upstream/master` is the remote-tracking reference for the official mathlib
  development branch. This fork does not keep a local `master` mirror or publish
  `origin/master`.
- `palomar/<slug>` branches contain separately maintained Palomar Registry
  delivery artifacts. They are not alternative default or general development
  branches and should not be merged wholesale into `main` merely to synchronize
  history.
- `exp/<slug>` may be used for mathematically or API-uncertain experiments.
- Formal Fidelity releases are published as immutable tags.

All publication goes to this fork's `origin`; nothing in this repository
authorizes pushes or pull requests to upstream. See
[AI_AGENT_PROJECT.md](AI_AGENT_PROJECT.md) for the complete maintenance policy.

## Upstream reconciliation

The rebase onto mathlib `v4.34.0` established the starting baseline. For later
updates, maintainers merge official stable mathlib release tags into local
`main`. They resolve conflicts, repair API fallout, and verify the result
before publishing with an authorized fast-forward push. Existing Fidelity
commit IDs remain in the history of `main`.
[Maintenance procedure](AI_AGENT_PROJECT.md#mathlib-baseline-reconciliation-workflow)

## Getting started

Use the official Lean release and standard library selected by `lean-toolchain`.
Field inversion and exact division require invertibility evidence. Use named
Euclidean quotients for division with remainder, including on `ℕ` and `ℤ`.
See the [arithmetic notation guide](Mathlib/Algebra/GroupWithZero/Checked/Notation.lean)
and [native quotient laws](Mathlib/Lean/Elab/NativeDivision.lean).

Install Lean and the supporting tools using the
[upstream mathlib instructions](https://leanprover-community.github.io/get_started.html),
then clone and build this fork:

```shell
git clone https://github.com/KiringYJ/mathlib-fidelity.git
cd mathlib-fidelity
git remote add upstream https://github.com/leanprover-community/mathlib4.git
git fetch upstream
lake exe cache get
lake build
```

For a focused build or the test suite:

```shell
lake build Mathlib.Import.Path
lake test
```

`lake test` builds the inherited suite in `MathlibTest/` and the fork's
regressions in `FidelityTest/`. Both suites are also available as build targets
with `lake build MathlibTest FidelityTest`.

Run `lake exe mk_all` after adding a new Mathlib module so that `Mathlib.lean`
remains current.

## Continuous integration

Fidelity CI builds and tests `main` pushes and pull requests targeting `main`
on GitHub-hosted Linux runners. It checks generated imports, both linter
families, and the regression tests and companion libraries. Each build records
the exact tested commit; pull requests test GitHub's merge commit with the base.
Separate weekly and manual runs also replay Mathlib and Batteries with
`leanchecker` and run the Mathlib test executable.

See [the CI guide](.github/CI.md) for validation scope, cache and resource
limits, and the upstream workflow isolation policy. The separate implementation
of the conjecture registry and proof-status admission gate is tracked in [issue #3](https://github.com/KiringYJ/mathlib-fidelity/issues/3).

## Using the fork as a dependency

This fork deliberately evolves independently of upstream's public API. Pin an
immutable Fidelity release tag for a durable dependency.

```lean
require mathlib from git
  "https://github.com/KiringYJ/mathlib-fidelity.git" @ "<release-tag>"
```

For evaluation, pin the exact commit from `main` that you tested.

The upstream
[dependency guide](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)
still applies to the surrounding Lake project setup.

## Contributing

Report bugs and propose changes through [GitHub Issues](https://github.com/KiringYJ/mathlib-fidelity/issues).

Pull requests to this fork are welcome when they follow the mathematical
fidelity, API, source, licensing, provenance, testing, and review requirements
in the [contribution guide](.github/CONTRIBUTING.md). Maintainers select and
schedule integration based on the work required to review, integrate, and
maintain eligible contributions.

The fork welcomes mathematics from every field, including specialized and
unpublished work. `Mathlib/` holds definitions and results that naturally
extend a mathematical theory. `Archive/` preserves standalone formalizations
of particular results and proofs. Both apply the same standards for
mathematical fidelity, proof status, provenance, and licensing.
[Placement policy](FORK_DESIGN.md#mathematical-scope-and-placement) ·
[Archive guide](Archive/README.md)

Maintainers handle integration conflicts and API fallout caused by upstream
reconciliation or fork-wide migrations. Contributors remain responsible for
the substance of their contribution.
[Pull request update policy](.github/CONTRIBUTING.md#updating-open-pull-requests)

External formalizations may arrive either through a pull request or through
maintainer-led curated intake. Contributions to this fork are not automatically
prepared, submitted, or forwarded as upstream mathlib pull requests.

## Project records

- [CHANGELOG.md](CHANGELOG.md) summarizes significant upstream and Fidelity changes by release.
- [Project maintenance guide](AI_AGENT_PROJECT.md#fidelity-gate) defines fidelity assessment and
  [library-wide audit procedures](AI_AGENT_PROJECT.md#full-library-fallback-audit).
- [FORK_DESIGN.md](FORK_DESIGN.md) sets the fork's library-wide design principles.
- [CONTRIBUTING.md](.github/CONTRIBUTING.md) gives admission, review, and testing requirements.
- [SOURCES.md](SOURCES.md) records external sources, candidate recovery
  priorities, licensing, provenance, integration mode, and status.
- [AI_AGENT_PROJECT.md](AI_AGENT_PROJECT.md) defines the repository workflow,
  branch policy, and verification requirements.

## Upstream resources

- [mathlib repository](https://github.com/leanprover-community/mathlib4)
- [Installation and learning resources](https://leanprover-community.github.io/get_started.html)
- [Generated mathlib documentation](https://leanprover-community.github.io/mathlib4_docs/)
- [Upstream contribution guide](https://leanprover-community.github.io/contribute/)
- [Lean community Zulip](https://leanprover.zulipchat.com)

## License

This repository is distributed under the [Apache License 2.0](LICENSE).
