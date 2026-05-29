<#
.SYNOPSIS
  Remove unnecessary #push-options / #pop-options pairs from an F* file.
  Uses the IDE full-buffer protocol for verification.
  Processes pairs last-to-first for optimal caching.

.PARAMETER File
  Path to the .fst file.

.PARAMETER DryRun
  Just list pairs without removing.

.PARAMETER LogFile
  Path for results log.

.PARAMETER WarmupTimeout
  Seconds for initial warmup. Default: 120.
#>
param(
    [Parameter(Mandatory=$true)]
    [string]$File,
    [switch]$DryRun,
    [string]$LogFile = "",
    [int]$WarmupTimeout = 120
)

# Self-contained script — IDE functions inlined below.

# ============================================================
# JSON ENCODING
# ============================================================

function ConvertTo-FstarJson2 {
    param([string]$s)
    $cap = [int]($s.Length + $s.Length / 10)
    $sb = [System.Text.StringBuilder]::new($cap)
    [void]$sb.Append('"')
    foreach ($ch in $s.ToCharArray()) {
        switch ([int]$ch) {
            34  { [void]$sb.Append('\"') }
            92  { [void]$sb.Append('\\') }
            10  { [void]$sb.Append('\n') }
            13  { [void]$sb.Append('\r') }
            9   { [void]$sb.Append('\t') }
            default {
                if ([int]$ch -lt 32) {
                    [void]$sb.Append(('\u{0:X4}' -f [int]$ch))
                } elseif ([int]$ch -gt 127) {
                    [void]$sb.Append(('\u{0:X4}' -f [int]$ch))
                } else {
                    [void]$sb.Append($ch)
                }
            }
        }
    }
    [void]$sb.Append('"')
    return $sb.ToString()
}

# ============================================================
# IDE SESSION
# ============================================================

function Start-Ide {
    param([string]$FilePath, [string]$WorkDir)
    $psi = New-Object System.Diagnostics.ProcessStartInfo
    $psi.FileName = "fstar.exe"
    $psi.Arguments = "--ide --cache_checked_modules --cache_dir obj $([System.IO.Path]::GetFileName($FilePath))"
    $psi.UseShellExecute = $false
    $psi.RedirectStandardInput = $true
    $psi.RedirectStandardOutput = $true
    $psi.RedirectStandardError = $true
    $psi.WorkingDirectory = $WorkDir
    $proc = [System.Diagnostics.Process]::Start($psi)
    $proc.BeginErrorReadLine()
    $proto = $proc.StandardOutput.ReadLine()
    if (-not ($proto -match '"protocol-info"')) {
        throw "Failed to start F* IDE: $proto"
    }
    return $proc
}

function Send-Cmd {
    param([System.Diagnostics.Process]$Proc, [string]$Json)
    $bytes = [System.Text.Encoding]::UTF8.GetBytes($Json + "`n")
    $Proc.StandardInput.BaseStream.Write($bytes, 0, $bytes.Length)
    $Proc.StandardInput.BaseStream.Flush()
}

function Send-Buffer {
    param([System.Diagnostics.Process]$Proc, [string]$Code, [string]$QueryId)
    $escaped = ConvertTo-FstarJson2 $Code
    $cmd = '{"query-id":"' + $QueryId + '","query":"full-buffer","args":{"kind":"full","code":' + $escaped + ',"with-symbols":false}}'
    Send-Cmd $Proc $cmd
}

function Wait-Buffer {
    param([System.Diagnostics.Process]$Proc, [int]$TimeoutSeconds = 300)
    $startedCount = 0; $okCount = 0; $failCount = 0; $failLine = -1
    $finished = $false
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    while (-not $finished -and $sw.ElapsedMilliseconds -lt ($TimeoutSeconds * 1000)) {
        if ($Proc.HasExited) { break }
        $line = $Proc.StandardOutput.ReadLine()
        if ($null -eq $line) { break }
        if ($line -match '"full-buffer-fragment-started"') { $startedCount++ }
        elseif ($line -match '"full-buffer-fragment-ok"') { $okCount++ }
        elseif ($line -match '"full-buffer-fragment-failed"') {
            $failCount++
            try { $parsed = $line | ConvertFrom-Json; $failLine = $parsed.contents.ranges.beg[0] } catch {}
        }
        elseif ($line -match '"full-buffer-finished"') { $finished = $true }
    }
    return @{ Started=$startedCount; OK=$okCount; Failed=$failCount; FailLine=$failLine; Elapsed=$sw.Elapsed }
}

function Stop-Ide {
    param([System.Diagnostics.Process]$Proc)
    try { Send-Cmd $Proc '{"query-id":"exit","query":"exit","args":{}}'; $Proc.WaitForExit(5000) } catch {}
    if (-not $Proc.HasExited) { $Proc.Kill() }
}

# ============================================================
# MAIN
# ============================================================

$fullPath = (Resolve-Path $File -ErrorAction Stop).Path
$workDir = [System.IO.Path]::GetDirectoryName($fullPath)

# Find all push-pop pairs
$lines = [System.IO.File]::ReadAllLines($fullPath)
$pairs = @()
$pushStack = @()
for ($i = 0; $i -lt $lines.Count; $i++) {
    if ($lines[$i] -match '^\s*#push-options\s+"([^"]+)"') {
        $pushStack += @{ Line = $i; Options = $Matches[1] }
    }
    elseif ($lines[$i] -match '^\s*#pop-options') {
        if ($pushStack.Count -gt 0) {
            $push = $pushStack[-1]
            $pushStack = $pushStack[0..($pushStack.Count-2)]
            $pairs += @{ PushLine = $push.Line; PopLine = $i; Options = $push.Options }
        }
    }
}

Write-Host "=== Remove Push-Pop Options ===" -ForegroundColor Cyan
Write-Host "File:    $File"
Write-Host "Pairs:   $($pairs.Count)"
Write-Host "Order:   last-to-first"
Write-Host ""

if ($DryRun) {
    Write-Host "(DRY RUN)" -ForegroundColor Yellow
    foreach ($p in ($pairs | Sort-Object { $_.PushLine } -Descending)) {
        Write-Host ("  L{0,4}-L{1,4}: {2}" -f ($p.PushLine+1), ($p.PopLine+1), $p.Options)
    }
    Write-Host ""
    Write-Host "$($pairs.Count) pairs found."
    return
}

# Start IDE
Write-Host "Starting F* IDE..." -NoNewline
$ideProc = Start-Ide $fullPath $workDir
Write-Host " OK" -ForegroundColor Green

# Warm cache
Write-Host "Warming cache..." -NoNewline
$content = [System.IO.File]::ReadAllText($fullPath)
$warmCode = $content.Replace("`r`n", "`n")
Send-Buffer $ideProc $warmCode "warm"
$warmResult = Wait-Buffer $ideProc -TimeoutSeconds $WarmupTimeout
if ($warmResult.Failed -gt 0) {
    Write-Host " FAILED" -ForegroundColor Red
    Stop-Ide $ideProc
    exit 1
}
Write-Host (" OK ({0} frags, {1:F1}s)" -f $warmResult.OK, $warmResult.Elapsed.TotalSeconds) -ForegroundColor Green
Write-Host ""

$changedCount = 0
$failedCount = 0
$log = @()

# Process last-to-first (by push line descending)
$sortedPairs = $pairs | Sort-Object { $_.PushLine } -Descending

try {
    foreach ($p in $sortedPairs) {
        $pushLn = $p.PushLine
        $popLn = $p.PopLine
        $opts = $p.Options
        
        Write-Host -NoNewline ("  L{0,4}-L{1,4} [{2}]  " -f ($pushLn+1), ($popLn+1), $opts)
        
        # Read current file, remove both lines
        $rawText = [System.IO.File]::ReadAllText($fullPath)
        $fileLines = $rawText -split "`r`n"
        
        # Find the actual current positions (lines may have shifted from prior removals)
        # Search for the exact push-options line text
        $pushText = $lines[$pushLn]
        $popText = $lines[$popLn]
        
        # Find in current file
        $currentLines = [System.IO.File]::ReadAllLines($fullPath)
        $pushIdx = -1; $popIdx = -1
        for ($i = 0; $i -lt $currentLines.Count; $i++) {
            if ($pushIdx -eq -1 -and $currentLines[$i] -eq $pushText) {
                # Verify the matching pop is nearby
                for ($j = $i+1; $j -lt $currentLines.Count; $j++) {
                    if ($currentLines[$j] -eq $popText) {
                        $pushIdx = $i; $popIdx = $j; break
                    }
                    if ($currentLines[$j] -match '^\s*#push-options') { break }
                }
            }
            if ($pushIdx -ge 0) { break }
        }
        
        if ($pushIdx -lt 0 -or $popIdx -lt 0) {
            Write-Host "not found" -ForegroundColor DarkYellow
            $log += "L$($pushLn+1)`t$opts`tnot-found"
            continue
        }
        
        # Remove both lines
        $newLines = @()
        for ($i = 0; $i -lt $currentLines.Count; $i++) {
            if ($i -eq $pushIdx -or $i -eq $popIdx) { continue }
            $newLines += $currentLines[$i]
        }
        $newRawText = ($newLines -join "`r`n") + "`r`n"
        
        # Verify
        $verifyCode = $newRawText.Replace("`r`n", "`n")
        $sw = [System.Diagnostics.Stopwatch]::StartNew()
        Send-Buffer $ideProc $verifyCode "pp$pushLn"
        $result = Wait-Buffer $ideProc -TimeoutSeconds 120
        
        if ($result.Failed -eq 0) {
            [System.IO.File]::WriteAllText($fullPath, $newRawText)
            Write-Host ("OK ({0:F1}s, {1} rechecked)" -f $sw.Elapsed.TotalSeconds, $result.Started) -ForegroundColor Green
            $log += "L$($pushLn+1)`t$opts`tok`t$($sw.Elapsed.TotalSeconds.ToString('F1'))s"
            $changedCount++
        } else {
            # Rollback IDE cache
            $origCode = $rawText.Replace("`r`n", "`n")
            Send-Buffer $ideProc $origCode "rb$pushLn"
            $null = Wait-Buffer $ideProc -TimeoutSeconds 120
            $failMsg = if ($result.FailLine -gt 0) { " (fail@L$($result.FailLine))" } else { "" }
            Write-Host ("FAIL$failMsg ({0:F1}s)" -f $sw.Elapsed.TotalSeconds) -ForegroundColor Red
            $log += "L$($pushLn+1)`t$opts`tfail`t$($sw.Elapsed.TotalSeconds.ToString('F1'))s"
            $failedCount++
        }
    }
}
finally {
    Stop-Ide $ideProc
}

Write-Host ""
Write-Host "=== Results ===" -ForegroundColor Cyan
Write-Host "  Removed:  $changedCount" -ForegroundColor Green
Write-Host "  Needed:   $failedCount" -ForegroundColor $(if ($failedCount -gt 0) { "Yellow" } else { "DarkGray" })

# Safety checks
$finalLines = (Get-Content $fullPath).Count
$expectedLines = $lines.Count - (2 * $changedCount)
$bytes = [System.IO.File]::ReadAllBytes($fullPath)
$loneLF = 0
for ($bi = 0; $bi -lt $bytes.Length; $bi++) {
    if ($bytes[$bi] -eq 10 -and ($bi -eq 0 -or $bytes[$bi-1] -ne 13)) { $loneLF++ }
}

$safe = $true
if ($finalLines -ne $expectedLines) {
    Write-Host "!!! LINE COUNT MISMATCH !!!" -ForegroundColor Red
    Write-Host "  Expected: $expectedLines (orig $($lines.Count) - 2*$changedCount removed)" -ForegroundColor Red
    Write-Host "  Actual:   $finalLines" -ForegroundColor Red
    $safe = $false
}
if ($loneLF -gt 0) {
    Write-Host "!!! CRLF SAFETY CHECK FAILED !!!" -ForegroundColor Red
    Write-Host "  Lone LF bytes found: $loneLF" -ForegroundColor Red
    $safe = $false
}
if ($safe) {
    Write-Host "  Safety:   $finalLines lines (expected), CRLF OK" -ForegroundColor Green
}

if ($LogFile) {
    $log | Out-File -FilePath $LogFile -Encoding UTF8
    Write-Host "Log: $LogFile"
}
