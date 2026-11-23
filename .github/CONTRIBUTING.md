# Contributing to mathlib-fidelity

External pull requests to `main` are welcome when they follow this fork's
policies. Read the [README](../README.md),
[Fork Design Philosophy and Roadmap](../FORK_DESIGN.md), and
[project-specific requirements](../AI_AGENT_PROJECT.md) before preparing a
change.

Policy compliance makes a contribution eligible for review; it does not
guarantee merger. Maintainers may request revisions or decline a contribution
because of scope, duplication, maintenance cost, or conflict with the fork's
design direction.

## Submission requirements

- Target `main` from a contributor-owned branch. Contributor branch names do
  not need to follow the repository's internal topic-branch taxonomy.
- Keep the change logically coherent and explain the mathematical or technical
  need it addresses.
- For a new theory or mathematical interface, show how it reuses existing
  results and composes with related constructions. Explain what determines
  any implicit mathematical structures or operations it introduces.
  [Interoperability between theories](../FORK_DESIGN.md#interoperability-between-mathematical-theories)
  and [priority-independent semantics](../FORK_DESIGN.md#priority-independent-mathematical-semantics)
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
whether the reviewed commit structure should be retained. Upstream-style merge
commits are not part of the maintained Fidelity patch stack.

## Moving `main` and integration responsibility

`main` is periodically rebased onto `upstream/master`, so its published history
and a pull request's merge base may change. Maintainers batch reconciliation,
avoid unnecessary rewrites during active review, and may temporarily freeze
reconciliation while a substantial pull request is close to merger. Before a
rewrite, maintainers inventory open pull requests and retain their old merge
bases and head object IDs ephemerally.

Contributors own the mathematical content, original implementation, and
responses to substantive review. Maintainers own integration conflicts and API
fallout caused solely by upstream reconciliation or fork-wide canonical API
migrations. Contributors are not expected to absorb repository-maintenance
churn unrelated to the substance of their contribution.

When the author enables **Allow edits from maintainers**, a maintainer may
prepare the rebase and resolve repository-driven fallout on the pull request
branch. A force-update may be used only after verifying that GitHub and the
branch rules permit it. This permission is optional and is not a condition for
review. Without it, the maintainer and contributor must coordinate the required
update. See
[GitHub's maintainer-edit documentation](https://docs.github.com/en/pull-requests/how-tos/work-with-forks/allowing-changes-to-a-pull-request-branch-created-from-a-fork).

Maintainer-driven updates replay only the contributor commits onto the new
`main`, using the retained old merge base. Any force-update of the pull request
branch must use its retained head object ID as an explicit force-with-lease;
bare force options are not permitted.

If the contributor's fork contains GitHub Actions workflows, GitHub may present
this permission as **Allow edits and access to secrets by maintainers**. Authors
should review GitHub's warning before enabling it; maintainers must not treat
workflow or secret access as ordinary integration authority.

## Mathematical and API requirements

- Preserve the intended mathematical objects, domains, hypotheses, and
  conclusions. Do not simplify a formal interface by weakening its mathematics
  or hiding a genuine definedness obligation.
- Follow the [official-Lean and operator-fidelity boundary](../FORK_DESIGN.md#official-lean-and-operator-fidelity).
  Exclude unfaithful operators from mathematical definitions and statements,
  including uses hidden by private helpers or aliases. Retain legitimate core
  types such as `Rat`. Remove replaceable uses from proofs and automation;
  record unavoidable official-toolchain proof dependencies and their faithful
  boundary. Keep official Lean unchanged and audit semantics rather than
  banning imports or every proof dependency.
- Prefer established mathematical vocabulary and natural theorem statements.
- Exercise new or changed APIs in real formalizations or meaningful regression
  tests when practical.
- State unresolved mathematical, implementation, or verification gaps
  explicitly.

Every migration follows the [complete-migration contract](../FORK_DESIGN.md#complete-migrations).
Internal experiments and incremental development are allowed; a prototype or
partial consumer migration is not a completed migration. Independent
foundational problems may remain separate TODO items, for example an XL issue
encountered during an L migration, provided the PR proves that its selected API
is faithful and identifies the lower-level dependency precisely. Required
in-scope proofs, consumer updates, and removals cannot be deferred this way.

## External sources and provenance

When a contribution copies, adapts, or reconstructs external material:

- identify the exact source and revision;
- verify compatible licensing, authorship, attribution, and applicable
  `NOTICE` obligations;
- report axioms, `sorry` declarations, generated artifacts, and overlap with
  existing declarations; and
- update [UPSTREAMS.md](../UPSTREAMS.md) when material is integrated into the
  fork.

A public repository or mathematically valid result is not sufficient evidence
that material may be redistributed or integrated unchanged. Maintainers may
canonicalize admitted material to this fork's public API and conventions while
preserving required provenance and attribution.

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
