# Fidelity continuous integration

Only the five reviewed files in `workflows/` are active. GitHub-hosted runners
execute them without upstream runner labels, Azure credentials, Zulip, bors,
or a local `master` branch. This configuration takes effect when published to
the repository; local validation does not establish a successful hosted run.

## Validation scope

| Workflow | Events | Checks |
| --- | --- | --- |
| `fidelity-ci.yml` | Push to `main`, PR to `main`, manual, reusable call | Workflow inventory, generated imports, source style, library build with warnings as errors, `MathlibTest`, `Archive`, `Counterexamples`, `Wanted`, test driver, environment linters |
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
lake build MathlibTest Archive Counterexamples Wanted
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
Existing fidelity regression tests run as part of `MathlibTest`. Build and
checker success do not by themselves certify mathematical statement fidelity.

## Revision and trust boundary

Every checkout explicitly selects `github.sha` and disables credential
persistence. For a PR this is GitHub's test merge commit with the base, rather
than an independently moving branch name. The Lean job verifies and records
that exact checkout SHA in its summary. A rebase changes the tested revision
and requires new checks.

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

After rebasing onto `upstream/master`, inspect upstream additions and modified
archived files before any push:

```shell
git diff --name-status upstream/master...main -- .github/workflows .github/upstream-workflows
python3 scripts/check_fidelity_workflows.py
python3 -B -m unittest discover -s scripts -p test_fidelity_workflows.py
```

New upstream files can reappear in the active directory even when existing
files were moved by an earlier Fidelity commit. Reconcile those files into
the inactive snapshot or deliberately review an added active workflow and
update the inventory. CI detection alone is too late to prevent an unreviewed
workflow from triggering on that first push, which is why this check is also
a pre-publication reconciliation requirement.
