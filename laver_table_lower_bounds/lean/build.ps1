param(
  [string]$LeanBin = '',
  [string]$Python = 'python',
  [ValidateRange(10,600)][int]$SecondsPerModule = 60,
  [switch]$Record
)
$ErrorActionPreference = 'Stop'
$taskArgs = @('-B', (Join-Path $PSScriptRoot 'build.py'), '--timeout', "$SecondsPerModule")
if ($LeanBin) { $taskArgs += @('--lean-bin', $LeanBin) }
if ($Record) { $taskArgs += '--record' }
& $Python @taskArgs
if ($LASTEXITCODE -ne 0) { throw "Lean build failed with exit code $LASTEXITCODE" }
