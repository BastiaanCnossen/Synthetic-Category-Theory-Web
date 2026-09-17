param([int]$Port = 8765, [string]$Python = '')
$ErrorActionPreference = 'Stop'
. (Join-Path $PSScriptRoot 'scripts\python-runtime.ps1')
$Python = Resolve-PilotPython -Requested $Python
Write-Host "Private local preview: http://127.0.0.1:$Port/index.html"
& $Python -m http.server $Port --bind 127.0.0.1 --directory (Join-Path $PSScriptRoot '_site')
