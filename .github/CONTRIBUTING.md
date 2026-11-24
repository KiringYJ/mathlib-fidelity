# Contributing to mathlib-fidelity

External pull requests to `main` are welcome when they follow this fork's
policies. Read the [README](../README.md),
[design charter](../FORK_DESIGN.md), and
[project-specific requirements](../AI_AGENT_PROJECT.md) before preparing a
change.

Policy compliance makes a contribution eligible for review. Maintainers may
request revisions, defer integration, or decline work for concrete reasons
such as duplication, design conflicts, or integration and maintenance costs.

## Submission requirements

- Target `main` from a contributor-owned branch. Contributor branch names do
  not need to follow the repository's internal topic-branch taxonomy.
- Keep the change logically coherent and explain the mathematical or technical
  need it addresses.
- For new formalizations, explain which results and prerequisites belong in
  `Mathlib/` or `Archive/` under the fork's
  [mathematical scope and placement policy](../FORK_DESIGN.md#mathematical-scope-and-placement).
- For a new theory or mathematical interface, show how it reuses existing
  results and composes with related constructions. Explain what determines
  any implicit mathematical structures or operations it introduces.
  Follow the principles for [interoperability between theories](../FORK_DESIGN.md#interoperability-between-mathematical-theories)
  and [priority-independent semantics](../FORK_DESIGN.md#priority-independent-mathematical-semantics).
- Write repository artifacts, commit messages, and PR descriptions in English;
  use Conventional Commit subjects and do not bypass repository hooks.
- Preserve existing public behavior unless the PR explicitly motivates and
  implements a complete migration. A migration must replace the selected API
  and all affected consumers together, without compatibility shims, deprecated
  aliases, dual APIs, or private transitional adapters.
- Run checks proportional to the affected modules and report the exact commands
  and results in the PR description.
- Do not include credentials, private paths, generated noise, or unrelated
  changes.

Maintainers normally integrate pull requests by rebase or squash, according to
whether the reviewed commit structure should be retained.

## Updating open pull requests

Upstream release merges preserve the published commits on `main`. An open pull
request may need an update if the merge introduces conflicts or changes APIs
that it uses.

Contributors own the mathematical content, original implementation, and
responses to substantive review. Maintainers own integration conflicts and API
fallout caused solely by upstream reconciliation or fork-wide canonical API
migrations. Contributors are not expected to absorb repository-maintenance
churn unrelated to the substance of their contribution.

When the author enables **Allow edits from maintainers**, a maintainer may
prepare a branch update and resolve repository-driven fallout. Writing to a
pull request branch also requires explicit authorization for the operation.
A force-update may be used only after verifying that GitHub and the
branch rules permit it. This permission is optional and is not a condition for
review. Without it, the maintainer and contributor must coordinate the required
update. See
[GitHub's maintainer-edit documentation](https://docs.github.com/en/pull-requests/how-tos/work-with-forks/allowing-changes-to-a-pull-request-branch-created-from-a-fork).

If a maintainer rebases the pull request branch, replay only the contributor
commits and use the captured pre-update head object ID as the explicit lease
for any force-update.
[Maintainer branch-update procedure](../AI_AGENT_PROJECT.md#updating-open-pull-requests)

If the contributor's fork contains GitHub Actions workflows, GitHub may present
this permission as **Allow edits and access to secrets by maintainers**. Authors
should review GitHub's warning before enabling it; maintainers must not treat
workflow or secret access as ordinary integration authority.

## Mathematical and API requirements

- Preserve the intended mathematical objects, domains, hypotheses, and
  conclusions, including genuine definedness obligations. For source-based
  results, document the correspondence between the source and the Lean
  statement. The same fidelity and proof standards apply to both `Mathlib/`
  and `Archive/`.
- Follow the [official-Lean and operator-fidelity boundary](../FORK_DESIGN.md#official-lean-and-operator-fidelity).
  Exclude unfaithful operators from mathematical definitions and statements,
  including uses hidden by private helpers or aliases. Retain legitimate core
  types such as `Rat`. Remove replaceable uses from proofs and automation;
  record unavoidable official-toolchain proof dependencies and their faithful
  boundary. Keep official Lean unchanged and audit semantics rather than
  banning imports or every proof dependency.
- Apply the [mathematical terminology policy](#mathematical-terminology).
- Follow the [regression coverage policy](#regression-coverage).
- State unresolved mathematical, implementation, or verification gaps
  explicitly.

Every migration follows the [complete-migration contract](../FORK_DESIGN.md#complete-migrations).
Internal experiments and incremental development are allowed; a prototype or
partial consumer migration is not a completed migration. Independent
foundational problems may remain separate TODO items, for example an XL issue
encountered during an L migration, provided the PR proves that its selected API
is faithful and identifies the lower-level dependency precisely. Required
in-scope proofs, consumer updates, and removals cannot be deferred this way.

## Mathematical terminology

Use the charter's [naming rules](../FORK_DESIGN.md#mathematical-vocabulary-first).
For a named result, supply evidence for the scope and spelling of its
conventional name and any primary or coequal formulations. Ordinarily
require two independent citable mathematical sources. Keep paper-local
names and attribution in the documentation. An author list alone gives
credit for the result and cannot establish a conventional theorem name.

Apply this review to new and deliberately renamed declarations. Check a
changed statement's own name for accuracy. Systematic renaming requires an
explicit task covering results with established names, their dependencies,
and complete consumer migration. Keep incidental work on existing proofs,
modules, or the upstream baseline outside that naming scope.

## Admission and review

The library welcomes mathematics from every field, including specialized and
unpublished work. Apply the same admission criteria regardless of journal
prestige, citation counts, popularity, research fashion, mathematical novelty
or importance, expected downstream use, or maintainer expertise. A single
result or construction can be a complete contribution. Preserve and reuse
existing formalizations where the audit supports it.

Admission requires a faithful, audited statement and a complete proof. The
adopted [proof-status policy](../FORK_DESIGN.md#conjectures-and-proof-status)
also provides for registered unresolved roots once the admission gate is
implemented. Disclose assumptions, axioms, trusted evaluation, generated
material, and proof status. External material also requires an exact source
revision, traceable provenance, and permission to copy, modify, and
redistribute each imported part. Establish a credible integration route
and plan deduplication where equivalent declarations already exist.

For source-based results, explain how the formal objects, domains, hypotheses,
and conclusions correspond to the source. Kernel checking verifies the Lean
statement under its actual dependencies. Mathematical review must also verify
that this statement expresses the intended result. Consult source literature
and relevant formalizations when reviewing unfamiliar material. AI may assist
with maintenance and mathematical review, but every review needs auditable
mathematical evidence.

Selected developments require audit, deduplication, adaptation to the maintained
API, and final verification. Differences in names, namespaces, imports,
abstraction, proof locality, and API usage are integration work. Keep raw
external snapshots as provenance evidence outside the public API. Record
candidates with open admission checks in the [source registry](../SOURCES.md#candidate-sources).
Maintainers select and schedule intake according to audit and migration
capacity, build time, dependencies, and integration and maintenance costs.

## Regression coverage

Retain appropriate regression coverage for every Fidelity-specific feature,
modification, and deliberate deviation from upstream. Keep inherited tests and
their ports in `MathlibTest/` and Fidelity-specific tests in `FidelityTest/`.
Organize modules by the main API or behavior under test, using mathlib's subject
directory names for mathematical tests.

State mathematical specifications in the public Lean API. Add regression
cases for interfaces, domains, tactics, elaboration, diagnostics, and important
consumers where existing proofs do not exercise the behavior. Test expected
failures when rejection is part of the contract. Enforce library-wide semantic
requirements with global linters and test those linters with focused fixtures.
Run `lake test` to build both test suites and report the checks performed.

## Recovery modes

Classify recovery work by its preservation goal.

- A **port** translates a Lean development whose mathematical organization and
  principal abstractions remain suitable.
- A **reconstruction** rebuilds selected, audited theorem coverage on current
  foundations when the former architecture has been superseded.
- A **reformalization** reproduces mathematics from another prover or a
  materially different foundation and requires a new trusted-boundary and
  foundation audit.

At the start of each recovery audit, search again for maintained descendants
and current library coverage. Map the selected source theorems and their
dependencies to current declarations, recording which results survive, have
been superseded, differ in statement, or remain unmatched. For a
reconstruction, reuse sound current infrastructure and reprove the unmatched
layer. Set theorem-level acceptance targets and verify the correspondence of
statements, hypotheses, constructions, and trusted proof boundaries at the
final integrated state. Apply the
[complete-migration contract](../FORK_DESIGN.md#complete-migrations).

Mathport relies on the port-era `#align` support. If translation preserves
useful structure, pair `mathport:v3-eol` with `mathlib4:v3-eol`, then upgrade
the result manually to the current baseline. Assess a reconstruction on
current APIs when the old foundations have been superseded. See the
[Mathport documentation](https://github.com/leanprover-community/mathport#readme).

Provisional recovery priorities and open audit questions are recorded with the
[candidate sources](../SOURCES.md#lean-3-preservation-and-reconstruction-leads).

## External sources and provenance

When a contribution copies, adapts, or reconstructs external material:

- identify the exact source and revision;
- verify compatible licensing, per-file authorship, attribution, third-party
  content, and applicable `NOTICE` obligations;
- report axioms, `sorry` declarations, generated artifacts, and overlap with
  existing declarations; and
- update [SOURCES.md](../SOURCES.md) when material is integrated into the
  fork.

A public repository or mathematically valid result does not establish permission
to redistribute material. Keep a source reference-only until compatible
licensing or permission is established. Maintainers adapt admitted material to
the API and conventions for its destination, preserve required copyright,
license, attribution, and `NOTICE` records, and mark modifications as required.
Record source revision, destination, changes, and verification so provenance
survives refactoring. Preserve the original authorship record.

## Pull request description

Describe:

- the problem and intended outcome;
- the mathematical or API design decisions;
- source and license information when external material is involved;
- verification performed; and
- known limitations or follow-up work.

For migrations, distinguish independently deferred foundational work from the
completed scope. Remaining obligations of the selected migration make it
incomplete; recording them as follow-up does not satisfy acceptance.

## Upstream boundary

Contributions here are for `mathlib-fidelity`. They are not automatically
prepared, submitted, or forwarded to `leanprover-community/mathlib4`. Anyone
who independently wants to contribute to upstream mathlib should follow the
[upstream contribution guide](https://leanprover-community.github.io/contribute/).
