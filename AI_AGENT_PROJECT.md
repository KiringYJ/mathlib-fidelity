# Project-Specific Agent Context

## Purpose

This fork is a personal, maintainer-curated downstream distribution of mathlib.
It uses the upstream implementation and theorem base while developing an
independent, mathematician-facing library whose public API prioritizes
mathematical fidelity and quality of life.

Fork-only changes are not intended for submission to upstream. Do not preserve,
split, or rewrite them merely for upstream pull-request acceptability. Upstream
remains a source of useful code and updates, not the target design authority for
this fork.

[FORK_DESIGN.md](FORK_DESIGN.md) is the library-wide design charter. It sets
the principles for semantics, API design, placement, and complete migrations.
Lean definitions and theorems specify individual APIs. Use module and
declaration docstrings to explain their mathematical meaning and design.
This file governs branch maintenance, reconciliation, the refactor protocol,
and verification. The [contribution guide](.github/CONTRIBUTING.md) owns
contributor-facing requirements.

The policies below are project-local overrides.

## Branch Model

- `main` is the canonical personal branch, GitHub default branch, and daily
  driver. It contains Fidelity changes and the history of reconciled mathlib
  releases. Publish updates as fast-forwards so existing commits remain in its
  history. The agent-workbench and fork-design files are tracked only on this
  personal line of development.
- `upstream/master` is the read-only remote-tracking reference for the official
  `leanprover-community/mathlib4:master` branch. Do not recreate a local
  `master` mirror or publish an `origin/master` branch merely to mirror it.
- `palomar/<slug>` branches are separately maintained delivery branches for
  Palomar Registry projects. Keep project-specific theorem, source, provenance,
  and review records inside the corresponding branch. Maintain their histories
  independently of `main` and keep general development on `main` or its topic
  branches.
- `exp/<slug>` may be used for work whose mathematical or API direction is not
  yet settled.
- Formal Fidelity releases are published as immutable tags.
- External pull requests target `main` from contributor-owned branches.
  Contributor branch names are not part of this repository's maintained branch
  taxonomy.

Do not infer authorization to push from a fetch, sync, or local branch update.
Publish Fidelity branches and releases only to `origin`. Target this fork
with project pull requests.

Keep logically independent Fidelity changes in separate, reviewable commits
on `main`.

## Mathlib Baseline Reconciliation Workflow

The rebase onto mathlib `v4.34.0` established the starting baseline. For each
subsequent batch, select an official stable tag from the
[mathlib releases](https://github.com/leanprover-community/mathlib4/releases)
and integrate it with a merge commit on local `main`. The command examples
use Bash.

1. Start on `main` with a clean working tree. Run
   `git fetch origin && git merge-base --is-ancestor origin/main main` and
   continue only on success. Unpublished Fidelity commits on `main` are allowed.
2. Set `release` to the selected upstream release tag. Fetch the tag directly
   into `FETCH_HEAD` and resolve its commit so a same-named local tag cannot
   select a different revision. Save the current `main` tip for workflow review.

   ```shell
   release=vX.Y.Z
   git fetch --no-tags upstream "refs/tags/$release" &&
     upstream_commit=$(git rev-parse --verify 'FETCH_HEAD^{commit}') &&
     pre_merge_main=$(git rev-parse --verify refs/heads/main)
   ```

3. Skip a release that is already integrated, as determined by
   `git merge-base --is-ancestor "$upstream_commit" main`. For a new release,
   run `git merge --no-ff --no-commit "$upstream_commit"` on `main`. Resolve
   conflicts and repair API fallout according to the fork's mathematical and
   API design while retaining sound upstream improvements. Finish the merge
   with a Conventional Commit subject such as `chore(upstream): merge mathlib vX.Y.Z`.
4. Verify that the merge commit has the pre-merge `main` tip as its first
   parent and the upstream release commit as its second. Run checks
   proportional to every affected module on the final `main`. Before
   publication, complete the
   [workflow diff review and inventory checks](.github/CI.md#preserved-upstream-automation-and-reconciliation)
   using the saved `pre_merge_main`.
5. After explicit publication authorization, push normally with
   `git push origin main:refs/heads/main`. The branch rules must permit merge
   commits and direct fast-forward updates. If the push is rejected because
   `origin/main` advanced, fetch and reconcile the remote commits, then verify
   the resulting revision before retrying.
6. Verify that local `main`, `origin/main`, and the live remote ref resolve to
   the same commit.

Use Git ancestry as the record of the reconciled baseline.

## Contributions and Curated External Source Intake

Follow the charter's [placement policy](FORK_DESIGN.md#mathematical-scope-and-placement)
for in-tree work, the [contribution guide](.github/CONTRIBUTING.md#admission-and-review)
for admission and review, and the [source registry](SOURCES.md#intake-procedure)
for the intake record and integration modes.

### Updating open pull requests

An upstream release merge preserves the existing `main` commits on which open
pull requests are based. Update a pull request when integration conflicts or API
changes require it. A maintainer writing to a contributor's branch needs both
the author's branch permission and explicit authorization for the operation.
Otherwise, coordinate the update with the contributor. Treat any accompanying
access to GitHub Actions workflow secrets as security-sensitive and use access
only for the authorized integration work.

Capture the pull request branch's head object ID before updating it. If the
update uses a rebase, identify the original merge base and replay only
the contributor commits, for example with
`git rebase --onto <new-main> <old-merge-base> <pr-branch>`. For a branch that
still uses the history before the `v4.34.0` rebase, verify the merge base in
that earlier Fidelity history. Before a force-update, confirm that the hosting
service and branch rules permit it and pass
`--force-with-lease=refs/heads/<remote-branch>:<old-head>` using the captured
head. If the live head has changed, fetch and incorporate the new contributor
commits before retrying with an updated lease.

### Intake procedure

Before copying or adapting external material, verify the exact source revision,
license and redistribution conditions, per-file authorship, third-party content,
`NOTICE` obligations, axioms, `sorry`s, generated artifacts, mathematical
status, and overlap with existing declarations. Record the source, in-tree
destination modules where applicable, and integration evidence in
`SOURCES.md`. If permission is absent or unclear, retain only a reference
until a separate license review establishes an authorized path.

## Design Contract

Before changing a public API, consult the matching principles in
[FORK_DESIGN.md](FORK_DESIGN.md#coequal-design-goals) and inspect the relevant
Lean definitions, theorems, and consumers. Apply the
[admission and source policies](#contributions-and-curated-external-source-intake)
to external material. Use the heuristics and refactor protocol below to
apply the charter to the selected scope.

### Official toolchain and operator dependency checks

Apply the [official-Lean and operator-fidelity boundary](FORK_DESIGN.md#official-lean-and-operator-fidelity)
to the selected operations and all affected packages. Validate an official
Lean version upgrade as a separate compatibility task.

Use the [operator-fidelity audit](.github/CI.md#operator-fidelity) and inspect
its proof dependency report. Test hidden semantic dependencies, retained
faithful operations, and the narrow toolchain exception when extending the
audit. Record each unavoidable official proof dependency and the evidence
for its boundary. For conjecture, axiom, and evaluation trust, follow the
separate [proof-status design](FORK_DESIGN.md#conjectures-and-proof-status)
and its implementation status in `TODO.md`.

## Working API Heuristics

These are review questions, not unconditional rules. Establish them against
concrete use cases before redesigning existing code.

- Is there a clear normal form for statements and theorem search?
- Does a coercion or typeclass hide a mathematical choice that users routinely
  need to vary explicitly?
- Does a partial operation preserve its domain obligation in the public type,
  proof arguments, or an explicit partiality type?
- Is each domain the exact canonical one, rather than a convenient sufficient
  condition or the narrower class for which one text names the operation?
- Can routine evidence be constructed and propagated automatically without
  concealing a genuine unresolved obligation?
- Can simplification, coercion insertion, or instance search erase a domain
  condition or silently select a totalized fallback?
- Does a predicate name identify what is measurable and whether measurability
  is ordinary or almost everywhere? Does order terminology distinguish a
  greatest element from a merely maximal one when the stronger result is proved?
- If a total object is claimed to be independently mathematical, which exact
  literature and specifying properties establish its degenerate cases? If it
  is the selected operation's fallback, is it removed? If it belongs to an
  independent lower-level problem, is its use proved faithful and recorded in
  a precise TODO entry?
- Can a thin facade improve semantic fidelity without duplicating a parallel
  theorem ecosystem?
- Does the migration replace the selected interface and all affected callers
  completely, while identifying any independently deferred foundational
  dependencies without claiming their removal?
- Does generated proof glue merely conceal an ontology mismatch? Automation
  and language models can assist discovery, but should not be used as evidence
  that a human-facing interface is already adequate.

Treat these as hypotheses to test through downstream code, not as blanket
claims about every mathlib module or maintainer. Keep criticism technical and
specific; do not put personal attacks in repository history, commits, issues,
or other project records.

## Complete Migration Workflow

Apply the complete-migration contract in `FORK_DESIGN.md` to every fork
migration, not only totalized APIs. It overrides the shared guide's default
preference for preserving backward compatibility. Deliver the final design for
the selected scope in one change, with no compatibility stage, dual API,
deprecated aliases, or private transitional adapters. Internal experiments,
incremental edits, and focused builds remain part of the same work; a
prototype-only delivery is not completion of an accepted migration.

An independent lower-level problem may be deferred: an L migration can finish
while an XL foundational issue is recorded in `TODO.md`. Identify the actual
declarations and obligation, and prove that the completed L interface is
faithful despite that dependency. This does not permit deferring callers or
proof obligations required by the selected L interface. Keep the completed
scope and deferred foundation distinct in the final report.

### Broad API refactor protocol

For an explicitly authorized public-API canonicalization:

1. Inventory the existing representations, notation, theorem families,
   instances, automation, and structurally different downstream consumers.
   Trace implicit entry points as well as named calls: inspect what bare
   ambient notation such as `volume` selects. Apply the charter's
   [mathematical fidelity rule](FORK_DESIGN.md#mathematical-fidelity) to enforce
   the same domain and canonicity at every entry point.
2. Separate ambient objects, propositions, and proof-carrying domains before
   choosing canonical syntax. State one normal form for each intended context
   and add regression tests for definitional equalities between retained
   surfaces.
   Test that insufficient hypotheses fail both at the named operation and at
   ambient instance inference. Also test explicit local constructors and routine
   sufficient conditions. Keep exact mathematical domains distinct from the
   narrower conditions used by automatic instances. Pin each negative test to
   its exact failure with `#guard_msgs`; `fail_if_success` also passes on
   unrelated errors. Give a default discharger's tactic syntax an explicit
   `(name := …)` and bound its search, so that failures stay fast and the
   syntax passes the environment linters.
3. Validate the replacement in real consumers during implementation.
   Closure-heavy proofs should use the operations of the structure that owns
   the invariant; cross a predicate-membership bridge only at an interface
   that genuinely requires the other form.
4. Remove the selected API's obsolete notation, aliases, ambient-only instances,
   and legacy subtype spellings across the repository. Do not introduce or
   retain public shims or private transitional adapters. Migrate all affected
   callers in the same change. Separately tracked lower-level dependencies must
   satisfy the proved-boundary requirements in `FORK_DESIGN.md`; they do not
   justify retaining the selected operation's old interface or implementation.
5. Rename declarations when their mathematical category changes, not merely
   their typography. Keep established terminology primary and implementation
   class names out of the public mathematical language.
6. During iteration, build the narrow affected modules. At the final source
   state, run `lake build`,
   `lake build MathlibTest FidelityTest Archive Counterexamples Wanted`, `lake test`,
   `lake lint`, `lake exe lint-style`, `lake exe mk_all --check`, and
   `git diff --check` for a cross-cutting refactor of this scale.
7. Add repository-wide negative scans for every removed surface, obsolete
   theorem name, compatibility shim, legacy representation, and newly added
   `sorry` or `admit`. Apply the operator-fidelity boundary when classifying
   hits: retained carriers and unavoidable toolchain proof dependencies are
   distinct from forbidden mathematical semantics and removable proof uses.
   Textual absence alone does not establish the boundary. A later core edit or
   byte-level normalization invalidates affected evidence and requires the
   relevant checks to be rerun.

When a style tool traverses transitive imports, distinguish errors introduced
by the current diff from pre-existing repository debt. Fix in-scope new errors
and report inherited failures accurately without expanding the refactor.

## Remaining Work

[`CHANGELOG.md`](CHANGELOG.md) records significant changes between consecutive Fidelity
releases, with separate entries for the mathlib baseline and the Fidelity API.
`TODO.md` tracks pending work. Completed entries can be removed once the Lean
API, any necessary docstrings, and
[regression coverage](.github/CONTRIBUTING.md#regression-coverage) preserve
their contracts. Resolve every obligation of the selected migration before
reporting it complete. Record independent foundational problems and other
separately scoped work in `TODO.md`. A TODO cannot substitute for
an in-scope proof, consumer migration, or removal. Remaining items include open
mathematical questions, hypotheses stronger than necessary,
deferred instances or API, unverified claims, and deferred reviewer
suggestions. An entry names the affected files and declarations, states the
obligation precisely, and records any known paper proof, counterexample, or
source. Before recording a question as open, check whether a short argument
settles it. A suggestion declined for a stated reason is a decision, not
remaining work; give the reason in the report. The final report points each
remaining item to the commit that resolved it or to its `TODO.md` entry.

## Using API credits

Use the workbench `openai-api-credits` skill for useful read-only migration
and TODO work when its PowerShell runner is available. Select the model
and reasoning effort with the active routing instructions. Supply relevant
Lean excerpts and exact Lake diagnostics, then verify accepted results with
local Lean and Lake under the project's review and build rules.

```powershell
$mathlibRunner = '.agents/skills/openai-api-credits/scripts/Invoke-OpenAIResponses.ps1'
& $mathlibRunner -ProjectRoot . -Prompt $mathlibPrompt -Model $selectedModel -ReasoningEffort $selectedEffort
```

The runner reads `CODEX_API_KEY` from the checkout's `.env`. Keep the file
locally Git-ignored and keep the key out of prompts, output, logs, and Git.
The subscription API grant covers Responses requests. The runner uses the
saved ChatGPT CLI sign-in for a read-only run when the API reports
`credit_balance_exhausted` or the key is absent. It surfaces other API errors.
Desktop chat billing follows its own sign-in.

## Architecture

- `Mathlib/` contains the canonical mathematical theory modules.
- `Mathlib.lean` is the generated import root and must be refreshed when new
  modules are added.
- [`Archive/`](Archive/README.md) contains standalone mathematical formalizations.
- `MathlibTest/` contains inherited and ported upstream tests. `FidelityTest/`
  contains Fidelity-specific regression tests.
- `Counterexamples/` and `scripts/` provide examples and repository tooling.
- `FORK_DESIGN.md` is the library-wide design charter.
- `SOURCES.md` records external source identity, candidate recovery priorities,
  license evidence, provenance, integration mode, and status.
- `AI_AGENT_GUIDE.md` is generated shared agent policy.
- `AI_AGENT_PROJECT.md` is the manually maintained policy for this fork and
  must be preserved verbatim by future workbench syncs.

## Build Commands

```powershell
lake exe cache get
lake build Mathlib.Import.Path
lake build
```

Use the narrow module build during iteration. A full build is proportional to
the scope and risk of the change; do not report it unless it actually ran.

## Test Commands

```powershell
lake build MathlibTest FidelityTest
lake test
lake exe mk_all
lake exe lint-style Mathlib.Import.Path
lake lint
```

Either test command builds both suites. Use `lake build MathlibTest FidelityTest`
with explicit Lake build flags when needed. Run `lake exe mk_all` when adding a
module to a generated import root. Lake discovers test modules from the suite globs.
CI also runs both linter families: `lake exe lint-style` applies the text-based style linters to the
listed modules and their imports, and `lake lint` runs the environment linters
(`batteries/runLinter`) over `Mathlib`. A successful build does not imply that
the environment linters pass; for example, they reject underscores in
automatically generated declaration names. For a narrow change,
`#lint in Mathlib.Import.Path` in a scratch file checks the affected module
before the full `lake lint`. Reuse relevant upstream documentation checks when
they remain applicable to the affected area.

## Important Files and Directories

- `README.md`: fork overview, branch model, setup, contribution policy, and
  upstream resource links.
- `FORK_DESIGN.md` sets library-wide design and migration principles.
- `SOURCES.md`: canonical source-repository and provenance registry.
- `TODO.md`: backlog of fidelity and API-hygiene work, with unresolved
  candidates subject to its fidelity gate.
- `.github/CONTRIBUTING.md`: contribution requirements for pull requests to
  this fork and the separate upstream boundary.
- `.github/PULL_REQUEST_TEMPLATE.md`: fork-specific submission prompts
  and verification checklist.
- `lakefile.lean` and `lean-toolchain`: project and Lean toolchain definitions.
- `.agent-workbench.yaml`: human-owned desired workbench configuration.
- `.agent-workbench.lock.json`: generated sync provenance and checksum ledger.

## Domain Terms

- **mathlib baseline**: `leanprover-community/mathlib4`, tracked by the local
  remote named `upstream`.
- **origin**: the personal fork `KiringYJ/mathlib-fidelity`.
- **daily driver**: `main`, the complete preferred working version and default
  branch.
- **source repository**: an external repository considered for reference,
  dependency, or curated integration; it is not automatically an authority or
  admitted dependency.
- **curated integration**: selection, audit, deduplication, faithful API
  migration, provenance capture, and final verification of external material.
- **mathematician-facing facade**: a thin public interface that exposes a
  mathematical concept naturally while reusing a sound generic core.
- **strict public API**: an interface whose ordinary mathematical operations
  expose their domains instead of relying on silent fallback values.
- **independent foundational dependency**: an existing lower-level API with a
  separately recorded problem; a completed scoped migration may use it only
  through a proved faithful boundary, without retaining its own retired API.

## Workspace Configuration

All agent-workbench managed paths are shared configuration for the personal
`main` branch and should be tracked there. Do not hide them through
`.git/info/exclude` or `.gitignore`.

Personal settings, credentials, caches, absolute machine paths, and runtime
state remain untracked. Future full syncs may update generated managed files
and the provenance ledger, but must never rewrite this project file.

## Project-Specific Constraints

- Follow [mathlib's source documentation conventions](https://mathlib.org/contribute/doc.html).
  Keep mathematical specifications in Lean definitions and theorems. Explain
  API choices and usage in the relevant module and declaration docstrings.
  For a cross-module API, link the related modules from an existing entry
  point. Keep API design and migration specifications in these docstrings.
- In file headers, name authors by their real names, as mathlib does:
  `Copyright (c) <year> <name>. All rights reserved.` and `Authors: <name>`.
  For a file written on the maintainer's behalf, take the name from
  `git config user.name`, which matches the maintainer's existing headers;
  never use a GitHub handle.
- Inspect the current branch before editing. Personal changes belong on `main`
  or an explicitly selected topic branch; use `upstream/master` only as the
  upstream development reference.
- Keep hooks enabled and follow the fork's naming, style, documentation, and
  verification requirements. Upstream conventions are useful defaults only
  where they do not conflict with `FORK_DESIGN.md`.
- Treat transcript discussions and API critiques as design evidence, not as
  authority for mathematical claims or statements about the current source.
- Verify current source and official documentation before asserting that an
  upstream API, theorem, or behavior still has a particular form.
- Do not add source remotes, dependencies, or imported code merely because a
  repository is mentioned. Require an explicit intake task and update
  `SOURCES.md` from verified evidence.
- Never infer redistribution permission from a public repository alone. Keep
  sources without a verified compatible license reference-only pending review,
  and preserve all applicable authorship, license, modification, and `NOTICE`
  records when integration is authorized.
- A recorded migration design or documentation update does not authorize Lean
  implementation. Once implementation is requested, complete the selected
  scope under the complete-migration contract, including its internal design
  experiments and final-state verification.
- Do not stage, commit, push, open a PR, or modify remote settings unless the
  current request authorizes that action. No project change is intended for an
  upstream PR.
