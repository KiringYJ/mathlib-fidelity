---
name: openai-api-credits
description: Use a project's OpenAI API credits for bounded code, proof, and review tasks through the Responses API. Apply when the user requests use of API credits or the project guide opts in to the runner.
---

<!-- agent-workbench: managed portable-skill -->

# OpenAI API Credits

## Dispatch

Use the routing table in `AI_AGENT_GUIDE.md` and resolve the task's model
and reasoning effort through the active platform binding. The parent prepares
the prompt and validates the result. Keep required independent review lanes.

## Setup

- Use PowerShell 7 and a project-root `.env` ignored by Git locally. Set
  `CODEX_API_KEY` to the project's OpenAI API key in that file.
- Keep keys and other `.env` contents out of prompts, output, and Git.
- For ChatGPT fallback, use Codex CLI with a saved ChatGPT sign-in.

Subscription API grants cover Responses API requests. [OpenAI API credits benefit](https://help.openai.com/en/articles/20001626-api-credits-benefit-for-eligible-chatgpt-subscriptions#use-the-credits-and-check-your-balance)

## Workflow

1. Write a bounded prompt with the task, relevant source excerpts, diagnostics,
   and acceptance criteria. The runner sends this text to the Responses API.
2. From the project root, invoke the synced runner with the selected model.

   ```powershell
   $runner = '.agents/skills/openai-api-credits/scripts/Invoke-OpenAIResponses.ps1'
   & $runner -ProjectRoot . -Prompt $taskPrompt -Model $model -ReasoningEffort $effort
   ```

3. Check the result against the current project and run its local validation.

The runner uses the saved ChatGPT sign-in in read-only mode when the project
key is absent or the API reports `credit_balance_exhausted`. It reports rate
limits, spending caps, and other API failures separately.
