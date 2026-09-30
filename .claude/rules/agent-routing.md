<!-- agent-workbench: managed platform-binding -->

# Claude Code Agent Routing

This binding resolves the workload tiers in `AI_AGENT_GUIDE.md` (**Skill Model
and Reasoning Routing**) to Claude Code models, effort levels, and subagents.
Claude Code loads it from `.claude/rules/`; other runtimes ignore it.

## Tier binding

User-selected starting allocation, adopted on 2026-10-01: mirror the Codex tier
structure and reserve Fable for critical-proof work. Treat it as provisional
until attributable task outcomes and the usage Claude Code reports support it;
API list prices are not a conversion to subscription usage.

| Tier | Model | Effort | Subagent |
| --- | --- | --- | --- |
| `peripheral` | `haiku` | none | `tier-peripheral` |
| `technical` | `sonnet` | `medium` | `tier-technical` |
| `mixed` | `sonnet` | `high` | `tier-mixed` |
| `research-math` | `opus` | `high` | `tier-research-math` |
| `critical-proof` | `fable` | `max` | `tier-critical-proof` |

The aliases follow the latest model in each family. On 2026-10-01 they resolve
to Haiku 4.5, Sonnet 5.5, Opus 5.5, and Fable 5.1 on the Anthropic API; Haiku
4.5 has no effort levels.

## Dispatch

- Delegate a tier through its subagent in `.claude/agents/`, which sets the
  tier's model and effort. The Agent tool takes a per-call `model` but no
  per-call effort, so a generic child cannot reproduce a tier's effort.
- Do not pass a per-call `model` to a tier subagent; it would replace the
  tier's model and keep its effort.
- Environment overrides such as `CLAUDE_CODE_EFFORT_LEVEL` and
  `CLAUDE_CODE_SUBAGENT_MODEL_FORCE`, organization model or effort limits, and
  model availability can change what actually runs. When a tier's settings are
  not honoured, report the recommended tier and the actual settings. As of
  2026-10-01, the Claude desktop app sets `CLAUDE_CODE_EFFORT_LEVEL` from its
  effort selector, and that variable overrides frontmatter `effort`, so tier
  subagents there keep their bound model but run at the session effort, except
  `peripheral`, which has none. Choose the session effort with that in mind,
  and report it as the actual effort when dispatching.
- For a named specialist, such as a plugin-provided agent, pass the tier's
  model as the per-call `model` when the specialist's definition differs. Its
  effort stays as defined, so report the recommended tier and actual effort
  when they differ.
- Invoking a skill does not change the main session's model or effort. Keep
  `model` and `effort` out of portable skill frontmatter; in Claude Code they
  switch the main session for the rest of the turn.
- The built-in `Explore` and `Plan` agents inherit the main session's model
  (Explore is capped at Opus on the Claude API) and skip project instructions,
  so they never see this binding. For peripheral search, use `tier-peripheral`,
  or call `Explore` with `model: haiku` and a self-contained prompt.
- When user-scope instructions or plugins suggest other models, follow this
  binding for work in this repository.

## Claude skill assignments

Only the portable workbench skills in `AI_AGENT_GUIDE.md` have rows so far.
Classify other Claude Code skills (bundled, plugin, or claude.ai-synced) by the
substance of each stage and report them as unmapped until they have rows here.
