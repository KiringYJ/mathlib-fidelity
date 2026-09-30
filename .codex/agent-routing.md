<!-- agent-workbench: managed platform-binding -->

# Codex Agent Routing

This binding resolves the workload tiers in `AI_AGENT_GUIDE.md` (**Skill Model
and Reasoning Routing**) to Codex models, reasoning effort, and dispatch
mechanics, and assigns tiers to Codex-environment skills. Codex reads it before
selecting a model or effort or dispatching a child; other runtimes ignore it.

## Tier binding

User-selected operating policy, adopted on 2026-09-07: optimize Codex allowance
per successfully completed, verified unit of work while accounting for both
engineering and research-level mathematics. These are working allocations,
not a measured universal Pareto frontier. Do not turn general intelligence
scores or coding benchmark dollars into research-math capability rankings or
weekly allowance percentages.

[Official OpenAI usage guidance](https://learn.chatgpt.com/docs/pricing)
distinguishes included ChatGPT-plan allowance from API-key billing and explains
that usage varies with the model and actual task. API benchmark cost is not a
direct conversion to the user's five-hour or weekly usage percentage. Keep
uncertainty explicit; validate allocation choices with attributable task-level
outcomes and host-reported usage when available.

| Tier | Model | Effort |
| --- | --- | --- |
| `peripheral` | `gpt-5.6-luna` | `max` |
| `technical` | `gpt-5.6-sol` | `medium` |
| `mixed` | `gpt-5.6-sol` | `high` |
| `research-math` | `gpt-6-astra` | `medium` |
| `critical-proof` | `gpt-6-astra` | `max` |

## Dispatch

When the native generic child surface supports overrides, dispatch its explicit
`model` and `reasoning_effort` fields separately, with `fork_turns` set to
`none` or a bounded recent history as the task needs. Keep model and effort
independent. Do not create fixed-combination agents or an agent definition for
each pair.

## OMX workflow compatibility

Ordinary scoped work stays direct; durable multi-goal execution uses Ultragoal.
Team is optional coordinated parallel work, not an automatic extra stage.

Explicit Autopilot preserves `deep-interview -> ralplan -> ultragoal`, durable
planning artifacts, sequential Architect/Critic reviews, and the session-bound
execution handoff. Ordinary progression does not require a host-issued consensus
receipt. Conductor-specific caller/parent/target proof applies only to an actual
Conductor operation; it must not become a blanket Autopilot prerequisite.

For Ultragoal finalization, the cleaner and independent code-reviewer/architect
lanes remain mandatory. Run the cleaner on the changed files and inspect its
result and diff. Reuse an accepted successful verification only when it covers
the current goal and final behavior, and its relevant source, tests,
configuration, dependencies, execution environment, and evidence validity are
unchanged. A no-change cleaner result alone does not establish that coverage.
Rerun affected checks for changed, uncovered, uncertain or time-sensitive inputs.
Record the actual verification run and validity basis in the required quality
gate evidence; do not fabricate a newer run. Complete the independent final
reviews after cleanup, and repeat affected review if later edits invalidate a
verdict. Preserve fresh goal snapshots, checkpoint receipts and all final gates.
This reuse rule never substitutes for the journal pipeline's source-bound
whole-manuscript final reviews.

## Codex skill assignments

These rows cover Codex-environment skills. The portable workbench skills are
assigned in `AI_AGENT_GUIDE.md`.

| Exact skill or explicit alias group | Tier | Delivery | Stage or escalation |
| --- | --- | --- | --- |
| `imagegen` | `peripheral` | Parent-bound tool | Prompt/edit planning only; the image tool controls its model. Complex implementation: `technical`; mathematical validity in a diagram: `research-math`. |
| `openai-docs` | `peripheral` | Bounded child | Source lookup and extraction. Nontrivial API implementation: `technical`; difficult integration or compatibility analysis: `mixed`. |
| `plugin-creator` | `peripheral` | Bounded child | Routine scaffolding and manifest updates. Nontrivial implementation: `technical`; cross-runtime architecture: `mixed`. |
| `skill-creator`, `skill-creator:skill-creator` | `technical` | Bounded child | Routine wording/metadata edits: `peripheral`; workflow design: `technical`; conflicting policies or specialist boundaries: `mixed`. |
| `skill-installer`, `plugin-management:plugin-management` | `peripheral` | Parent-bound tool | Known-source installation and listing. Substantive failure diagnosis: `technical`; complex reconciliation: `mixed`. Preserve action authorization. |
| `ai-slop-cleaner`, `oh-my-codex:ai-slop-cleaner` | `peripheral` | Leader workflow | Behaviour-preserving cleanup with established tests: `peripheral`; nontrivial refactor: `technical`; contract/architecture decisions: `mixed`. Mathematical semantics use the workload override. |
| `analyze`, `oh-my-codex:analyze` | `technical` | Bounded child | Gather repository evidence with `peripheral`; complex causal analysis: `mixed`. Theorem validity or proof-gap analysis goes directly to `research-math`. |
| `autopilot`, `oh-my-codex:autopilot` | `technical` | Leader workflow | Parent coordinates. Peripheral work: `peripheral`; implementation: `technical`; difficult technical review: `mixed`. Classify each child stage; mathematical content uses `research-math` or `critical-proof` directly. |
| `claude-code-setup:claude-automation-recommender` | `technical` | Bounded child | Inventory: `peripheral`; capability recommendations: `technical`; cross-project architecture: `mixed`. |
| `claude-md-management:claude-md-improver`, `claude-md-management:source-command-revise-claude-md` | `peripheral` | Bounded child | Grounded documentation updates. Conflicting project policies: `technical`; complex authority or architectural decisions: `mixed`. |
| `code-review`, `oh-my-codex:code-review` | `mixed` | Leader workflow | Independent code/spec and architect lanes: `mixed`. Mathematical claims: `research-math`; main-theorem, formal-proof, or adversarial proof audit: `critical-proof`. Preserve both independent outputs and the unavailable-review gate. |
| `computer-use:computer-use` | `peripheral` | Parent-bound tool | Routine UI operations and extraction. Multi-system technical troubleshooting: `technical`. Preserve the active session; interpret mathematical content using the workload override. |
| `deep-interview`, `oh-my-codex:deep-interview` | `mixed` | Leader workflow | Parent owns questions and answers. Ordinary requirements use `mixed`; resolving mathematical hypotheses or problem formulation uses `research-math`, without a cheap-first requirement. |
| `deep-research-work:deep-research` | `mixed` | Bounded child | Literature retrieval/metadata: `peripheral`; non-mathematical synthesis: `mixed`; mathematical substance: `research-math`; main-theorem, proof search, or adversarial proof audit: `critical-proof`. |
| `doctor`, `oh-my-codex:doctor` | `technical` | Parent-bound tool | Routine inspection: `peripheral`; technical diagnosis: `technical`; complex runtime interactions: `mixed`. If a formalization failure may be mathematical, classify that question as `research-math`. |
| `documents:documents`, `pdf:pdf`, `presentations:Presentations`, `spreadsheets:Spreadsheets` | `peripheral` | Parent-bound tool | Formatting, extraction, and writing an already-established argument: `peripheral`; nontrivial artifact code: `technical`. Evaluating the mathematical argument itself uses `research-math` or `critical-proof`. Preserve visual QA. |
| `help`, `oh-my-codex:hud`, `oh-my-codex:cancel`, `ralph-loop:source-command-help`, `ralph-loop:source-command-cancel-ralph` | `peripheral` | Parent-bound tool | Status, help, and requested control operations. Substantive diagnosis follows its own skill row. |
| `hookify:source-command-configure`, `hookify:writing-hookify-rules` | `peripheral` | Parent-bound tool | Routine rule/configuration edits. Enforcement logic: `technical`; difficult trust-boundary interactions: `mixed`. |
| `hookify:source-command-list` | `peripheral` | Parent-bound tool | Read-only listing and concise explanation. |
| `oh-my-codex:ask` | `peripheral` | Parent-bound tool | Prepare the grounded advisor question; the external advisor has its own configuration. Evaluate technical claims with `mixed`, mathematical claims with `research-math`, and critical proofs with `critical-proof`. |
| `oh-my-codex:autoresearch` | `mixed` | Leader workflow | Parent owns evaluator gates. Routine experiments: `technical`; mathematical research: `research-math`; new formal proof search or high-failure-cost proof obligations: `critical-proof`. |
| `oh-my-codex:best-practice-research` | `peripheral` | Bounded child | Official-source retrieval and comparison. Implementation implications: `technical`; material technical tradeoffs: `mixed`; mathematical validity: `research-math`. |
| `oh-my-codex:configure-notifications` | `peripheral` | Parent-bound tool | Requested configuration/status. Nontrivial provider failures: `technical`. |
| `oh-my-codex:design` | `technical` | Leader workflow | Product/UI design: `technical`; complex engineering tradeoffs: `mixed`. Mathematical modeling decisions use `research-math`. |
| `oh-my-codex:omx-setup`, `omx-setup` | `peripheral` | Parent-bound tool | Routine setup and configuration inspection. Technical diagnosis: `technical`; difficult cross-runtime interactions: `mixed`. |
| `oh-my-codex:performance-goal` | `mixed` | Leader workflow | Parent owns measurements and evaluator gates. Bounded implementation: `technical`; difficult engineering: `mixed`; mathematical correctness of an algorithm/model: `research-math`. Preserve measured acceptance criteria. |
| `oh-my-codex:ultragoal`, `oh-my-codex:ultraqa`, `ultraqa` | `technical` | Leader workflow | Parent owns lifecycle state. Peripheral tasks: `peripheral`; nontrivial implementation: `technical`; difficult integration: `mixed`. Mathematical or critical-proof stages use `research-math` or `critical-proof` directly. |
| `oh-my-codex:plan`, `plan`, `oh-my-codex:ralplan`, `ralplan` | `technical` | Leader workflow | Technical planning: `technical`; difficult engineering criticism: `mixed`. Research-math planning: `research-math`; critical proof strategy or a long lemma chain: `critical-proof`. |
| `oh-my-codex:skill` | `peripheral` | Parent-bound tool | Inspect/manage skills; installation and authoring use their respective rows. |
| `oh-my-codex:team`, `team` | `technical` | Leader workflow | Parent coordinates; classify worker stages separately. Peripheral: `peripheral`; technical: `technical`; difficult integration: `mixed`; mathematics: `research-math`; critical proof: `critical-proof`. Host settings govern actual workers. |
| `oh-my-codex:visual-ralph` | `mixed` | Leader workflow | Visual iteration and nontrivial technical comparison: `mixed`; routine visual fixes: `peripheral`. Preserve evidence and state; mathematical semantics follow the workload override. |
| `oh-my-codex:wiki` | `peripheral` | Parent-bound tool | Grounded summaries and updates. Taxonomy design: `technical`; validation of new mathematical connections: `research-math`. |
| `oh-my-codex:worker` | `peripheral` | Bounded child | Peripheral worker default. Technical implementation: `technical`; difficult math/code integration using established results: `mixed`; mathematical substance: `research-math`; critical proof: `critical-proof`. The Team host assigns actual settings. |
| `security-review` | `mixed` | Bounded child | Independent technical security review: `mixed`. A critical adversarial audit with unusually high failure cost may start directly at `critical-proof`. |
| `sites:sites-building` | `technical` | Parent-bound tool | Routine scaffolding/content: `peripheral`; nontrivial site implementation: `technical`; complex architecture: `mixed`. Preserve the Sites session. |
| `sites:sites-hosting` | `peripheral` | Parent-bound tool | Routine authorized deployment/status. Technical failure diagnosis: `technical`; complex infrastructure interactions: `mixed`. |
| `spreadsheets:excel-live-control` | `peripheral` | Parent-bound tool | Routine edits and established formulas: `peripheral`; complex workbook code/integration: `technical`. Mathematical model validity: `research-math`. Preserve the live Excel session. |
| `template-creator:template-creator` | `peripheral` | Bounded child | Routine reusable artifact production and QA. Nontrivial generation logic: `technical`; difficult technical integration: `mixed`. |
| `visualize:visualize` | `peripheral` | Parent-bound tool | Explanatory visuals for established content: `peripheral`; simulation implementation: `technical`; validity of the mathematical model or argument: `research-math`. |
| `web-clone` | `technical` | Leader workflow | Parent owns browser evidence. Routine markup/styles: `peripheral`; nontrivial behaviour: `technical`; difficult cross-system debugging: `mixed`. |
