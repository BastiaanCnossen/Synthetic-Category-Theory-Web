param([switch]$Frozen, [switch]$ReuseAgdaCheck, [switch]$ManuscriptOnly, [string]$Python = '')
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'scripts\python-runtime.ps1')
$Python = Resolve-PilotPython -Requested $Python
$buildArguments = @((Join-Path $PSScriptRoot 'scripts\build.py'))
if ($Frozen) { $buildArguments += '--frozen' }
if ($ReuseAgdaCheck) { $buildArguments += '--reuse-agda-check' }
if ($ManuscriptOnly) { $buildArguments += '--manuscript-only' }
& $Python @buildArguments
if ($LASTEXITCODE -ne 0) { throw 'Web edition build failed. See _build logs.' }
