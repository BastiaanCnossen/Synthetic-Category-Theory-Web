function Resolve-PilotPython {
    param([string]$Requested = '')
    $pilotCandidates = @()
    if ($Requested) {
        $pilotCandidates += $Requested
    } else {
        foreach ($pilotName in @('python', 'python3')) {
            $pilotCommand = Get-Command $pilotName -CommandType Application -ErrorAction SilentlyContinue
            if ($pilotCommand) { $pilotCandidates += $pilotCommand.Source }
        }
        $pilotCandidates += Join-Path $env:USERPROFILE '.cache\codex-runtimes\codex-primary-runtime\dependencies\python\python.exe'
    }
    foreach ($pilotCandidate in ($pilotCandidates | Select-Object -Unique)) {
        if (-not (Test-Path -LiteralPath $pilotCandidate)) { continue }
        try {
            $null = & $pilotCandidate -c 'import sys; sys.exit(0 if sys.version_info >= (3, 10) else 1)' 2>$null
            if ($LASTEXITCODE -eq 0) { return $pilotCandidate }
        } catch {
            # App-execution aliases can exist without an installed interpreter.
        }
    }
    throw 'A working Python 3.10+ interpreter is required. Pass -Python with its executable path.'
}
