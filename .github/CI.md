# Fidelity continuous integration

Only the five reviewed files in `workflows/` are active. GitHub-hosted runners
execute them without upstream runner labels, Azure credentials, Zulip, bors,
or a local `master` branch. This configuration takes effect when published to
the repository; local validation does not establish a successful hosted run.

## Validation scope

| Workflow | Events | Checks |
| --- | --- | --- |
| `fidelity-ci.yml` | Push to `main`, PR to `main`, manual, reusable call | Workflow inventory, generated imports, source style, library build with warnings as errors, `MathlibTest`, `FidelityTest`, `Archive`, `Counterexamples`, `Wanted`, test driver, environment linters |
| `fidelity-proof-check.yml` | Monday at 02:23 UTC, manual | All Fidelity CI checks, fresh-kernel replay of `Mathlib` and `Batteries`, Mathlib test executable |
| `actionlint.yml` | Changes under `.github/` on `main` pushes and PRs, manual | Workflow syntax, expressions, shell snippets, SHA-pinned action references |
| `pre-commit.yml` | Push to `main`, PR to `main`, manual | Repository pre-commit hooks, without automated writeback |
| `cache_test.yml` | Cache/toolchain/configuration changes on `main` pushes and PRs, manual | Existing network-free cache unit tests on Linux and Windows |

Workflow policy, source hygiene, and workflow linting give feedback separately
from the full Lean build. The full job runs these commands in order and fails
on the first unsuccessful check:

```shell
lake exe cache get --cache-from=master,legacy
lake exe mk_all --check
lake build --wfail
lake build MathlibTest FidelityTest Archive Counterexamples Wanted
lake test
lake lint
lake exe lint-style
```

The scheduled/manual proof workflow calls that same workflow and inserts the
following steps before the final source-style check. A source-style failure
still fails the workflow, while allowing the distinct kernel checks to run
after successful compilation, tests, and environment linting:

```shell
lake env leanchecker --fresh Mathlib
lake env leanchecker --fresh Batteries
lake exe mathlib_test_executable
```

The bundled `leanchecker` replays declarations through Lean's kernel; it is
not an independently implemented verifier or an axiom admission audit. No
nanoda result is claimed by these workflows. The conjecture registry, named
root dependency analysis, reviewed axiom base, and three-status admission gate
remain the separate accepted implementation tasks in
[`TODO.md`](../TODO.md#conjectures-and-proof-status----accepted-design-pending-implementation).
The `lake test` driver builds both `MathlibTest` and `FidelityTest`.
Mathematical statement fidelity is evaluated under the
[fork design policy](../FORK_DESIGN.md#mathematical-fidelity).

## Operator fidelity

`lake lint` runs the [Mathlib operator audit](../FidelityTest/Linter/OperatorFidelityFull.lean)
before the environment linters. The test target also runs that audit. It
loads private declarations and rejects retired dependencies in statements,
predicate bodies, and mathematical data. The proof report records the
declarations and ownership of proof uses and fails if traversal is incomplete.
Review the report against the
[official Lean boundary](../FORK_DESIGN.md#official-lean-and-operator-fidelity).

After building the companion packages, run
`python scripts/operator_fidelity_packages.py` to audit `Archive`,
`Counterexamples`, `Wanted`, `MathlibTest`, and `FidelityTest`. The script
reports each package separately. The deliberate negative fixture runs in
its own regression target. See the
[audit implementation](../Mathlib/Tactic/Linter/OperatorFidelity.lean) for
the current retired operators and report commands.

The [retired-instance policy](../Mathlib/Lean/Elab/OperatorPolicy.lean)
suppresses selected core instances in covered commands at elaboration time.
The declaration audit checks the resulting dependencies, including explicit
references and generated declarations in its scope. The general
[priority-independent elaboration checks](../TODO.md#priority-independent-elaboration)
remain pending.

## Workflow lint before pushing

Install the `pre-push` hook in each clone used to publish `main`. It runs
`actionlint` with ShellCheck on the active workflows in the outgoing commit.
A missing tool or a lint failure stops the push.

The hook requires Python 3, actionlint, and ShellCheck. Use the actionlint version
pinned in `workflows/actionlint.yml`. Put the linter executables on `PATH` or in
`fidelity-ci/bin` under the directory returned by `git rev-parse --git-common-dir`.
Run the following from the repository root in Bash, using Git Bash on Windows.

```shell
hook=$(git rev-parse --git-path hooks/pre-push)
if test -e "$hook"; then
  printf 'Integrate the workflow lint hook with the existing hook at %s\n' "$hook" >&2
else
  install -m 0755 .github/hooks/pre-push "$hook"
fi
```

## Revision and trust boundary

Every checkout explicitly selects `github.sha` and disables credential
persistence. For a PR this is GitHub's test merge commit with the base, rather
than an independently moving branch name. The Lean job verifies and records
that exact checkout SHA in its summary. Rerun affected checks when the tested
revision changes, including after an upstream release merge changes a PR's
test merge commit.

Contributor code runs only through `pull_request` with `contents: read`.
The workflows neither inherit secrets nor request OIDC, PR write, or repository
write permissions. The scheduled checker uses the default branch revision
captured by its triggering event. A manual run uses the selected ref's event
SHA. No workflow posts messages, merges PRs, tags releases, or publishes caches
to upstream services.

## Caches and hosted-runner limits

The full job uses `ubuntu-24.04`, two Lean threads, and a six-hour timeout.
It removes unused Android, .NET, and GHC installations from the disposable
hosted VM to make room for Lean artifacts. Cold full builds can still exhaust
hosted memory, disk, or time; such a failure is a failed full check, never a
successful reduced-scope build. Measure the first hosted run before selecting
different capacity or shard boundaries.

The GitHub cache contains only `.lake/build` and `.lake/packages`. Keys include
OS, architecture, the toolchain/Lake configuration/manifest hash, and exact
commit SHA; compatible earlier caches are restored as incremental build inputs.
Lake still checks build traces and rebuilds changed sources and dependencies.
Only successful `main` push builds save caches. PR and scheduled runs restore
but do not save. Cache quotas and eviction can make a run cold again.

Public upstream cache downloads use only the `master` and `legacy` containers.
No fork namespace, unsafe history walk, upload credential, or cache-write OIDC
is used. Fork changes to `lakefile.lean` or dependencies can invalidate all
upstream artifact hashes, so these downloads are an optimization rather than
a substitute for a full fork build.

## Preserved upstream automation and reconciliation

`upstream-workflows/` preserves the inherited workflows byte for byte as
inactive reference material. GitHub only discovers workflow YAML directly
under `.github/workflows/`; the archived bot, release, privileged PR, daily,
and reusable-build workflows are not executable entry points. Supporting
`.github/actions/` and upstream scripts remain in place for reference. Do not
call archived reusable workflows from an active workflow.

After merging an upstream release, review the workflow diff against the
`pre_merge_main` tip saved in the
[reconciliation procedure](../AI_AGENT_PROJECT.md#mathlib-baseline-reconciliation-workflow).
The merge commit's first parent identifies that tip for later reviews. Run
the inventory check and its tests before publication.

```shell
git diff "$pre_merge_main" main -- .github/workflows .github/upstream-workflows
python3 scripts/check_fidelity_workflows.py
python3 -B -m unittest discover -s scripts -p test_fidelity_workflows.py
```

An upstream merge can add workflow files alongside the reviewed active ones.
Move inherited additions into the inactive snapshot, or explicitly review and
admit them and update the inventory. Complete that review locally before the
first push, which can trigger any newly active workflow.
