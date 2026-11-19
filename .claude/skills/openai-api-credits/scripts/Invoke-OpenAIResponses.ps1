#Requires -Version 7.0
[CmdletBinding()]
param(
    [Parameter(Mandatory, Position = 0)]
    [string] $Prompt,

    [Parameter(Mandatory)]
    [string] $Model,

    [string] $ProjectRoot = '.',

    [string] $ReasoningEffort,

    [int] $MaxOutputTokens = 4096
)

$ErrorActionPreference = 'Stop'
$PSNativeCommandUseErrorActionPreference = $false

$projectDirectory = Get-Item -LiteralPath $ProjectRoot
if ($projectDirectory -isnot [System.IO.DirectoryInfo]) {
    throw 'ProjectRoot must identify a filesystem directory.'
}
$projectPath = $projectDirectory.FullName
$keyFile = Join-Path $projectPath '.env'
$projectKey = $null
if (Test-Path -LiteralPath $keyFile -PathType Leaf) {
    $keyEntry = Select-String -LiteralPath $keyFile -CaseSensitive -Pattern '^\s*(?:export\s+)?CODEX_API_KEY\s*=(?<value>.*)$' |
        Select-Object -Last 1
    if ($keyEntry) {
        # Accept bare or quoted values and inline comments without evaluating the file.
        $keyValue = [regex]::Match(
            $keyEntry.Matches[0].Groups['value'].Value,
            '^\s*(?:"(?<key>[^"]*)"|''(?<key>[^'']*)''|(?<key>[^\s#''"]*))\s*(?:#.*)?$')
        if (-not $keyValue.Success) {
            throw 'Invalid CODEX_API_KEY assignment in the project .env.'
        }
        $projectKey = $keyValue.Groups['key'].Value
    }
}

if ($projectKey) {
    Write-Host 'Running through the OpenAI Responses API.'
    $requestBody = @{
        model = $Model
        input = $Prompt
        max_output_tokens = $MaxOutputTokens
        service_tier = 'default'
        store = $false
    }
    if ($ReasoningEffort) {
        $requestBody.reasoning = @{ effort = $ReasoningEffort }
    }
    $request = @{
        Uri = 'https://api.openai.com/v1/responses'
        Method = 'Post'
        Headers = @{ Authorization = "Bearer $projectKey" }
        ContentType = 'application/json'
        Body = $requestBody | ConvertTo-Json -Depth 4 -Compress
        SkipHttpErrorCheck = $true
        StatusCodeVariable = 'responsesHttpStatus'
        TimeoutSec = 120
    }
    try {
        $response = Invoke-RestMethod @request
    } catch {
        throw 'The OpenAI Responses request ended without a usable HTTP response.'
    }

    if ($responsesHttpStatus -eq 429 -and $response.error.code -eq 'credit_balance_exhausted') {
        Write-Host 'API credits are exhausted. Switching to the saved ChatGPT sign-in.'
    } else {
        if ($responsesHttpStatus -ne 200) {
            throw "OpenAI Responses failed with HTTP $responsesHttpStatus and error code '$($response.error.code)'."
        }

        $responseText = ($response.output |
            Where-Object { $_.type -eq 'message' -and $_.role -eq 'assistant' } |
            ForEach-Object { $_.content } |
            Where-Object type -eq 'output_text' |
            ForEach-Object { $_.text }) -join [Environment]::NewLine
        if ($response.usage) {
            Write-Host "OpenAI API usage: $($response.usage.input_tokens) input, $($response.usage.output_tokens) output tokens."
        }
        if ($responseText) {
            Write-Output $responseText
        }
        if ($response.status -ne 'completed' -or [string]::IsNullOrWhiteSpace($responseText)) {
            throw "OpenAI Responses returned status '$($response.status)' without a complete text answer. $($response.incomplete_details.reason)"
        }
        exit 0
    }
} else {
    Write-Host 'The project API key is absent. Using the saved ChatGPT sign-in.'
}

$previousCodexKey = $env:CODEX_API_KEY
$previousOpenAIKey = $env:OPENAI_API_KEY
try {
    $env:CODEX_API_KEY = $null
    $env:OPENAI_API_KEY = $null
    $loginStatus = & codex login status 2>&1 | Out-String
    if ($LASTEXITCODE -ne 0 -or $loginStatus -notmatch '(?m)^[ \t]*Logged in using ChatGPT[ \t]*\r?$') {
        throw 'A saved ChatGPT CLI sign-in is required for fallback.'
    }

    $codexArguments = @(
        'exec', '-C', $projectPath, '--sandbox', 'read-only',
        '-m', $Model,
        '-c', 'model_provider="openai"',
        '-c', 'forced_login_method="chatgpt"',
        '-c', 'approval_policy="never"'
    )
    if ($ReasoningEffort) {
        $codexArguments += @('-c', "model_reasoning_effort=$ReasoningEffort")
    }
    & codex @codexArguments $Prompt
    exit $LASTEXITCODE
} finally {
    $env:CODEX_API_KEY = $previousCodexKey
    $env:OPENAI_API_KEY = $previousOpenAIKey
}
