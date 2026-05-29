<#
.SYNOPSIS
  F* IDE-accelerated refactoring framework.
  
  Uses the F* IDE protocol (full-buffer mode) for incremental verification,
  achieving 10-50x speedup over standalone fstar.exe invocations.

.DESCRIPTION
  Modes:
    -Mode count     : Print number of definitions in the file.
    -Mode list      : Print index + first line of each definition.
    -Mode get       : Print definition by -Index or -Name.
    -Mode transform : Apply -Script to definitions in range.
                      Verifies using IDE full-buffer; rolls back on failure.

  The transform mode processes definitions from LAST to FIRST by default
  (optimal for IDE caching: prefix remains cached for each edit).

.PARAMETER File
  Path to the .fst or .fsti file to operate on.

.PARAMETER Mode
  One of: count, list, get, transform.

.PARAMETER Index
  (get mode) 0-based index of the definition to retrieve.

.PARAMETER Name
  (get mode) Name of the definition to retrieve.

.PARAMETER From
  (transform mode) Start index (inclusive). Default: 0.

.PARAMETER To
  (transform mode) End index (exclusive). Default: definition count.

.PARAMETER Script
  (transform mode) Path to a transform script. Receives:
    $Definition  - string content of the definition
    $Index       - 0-based definition number
    $Name        - name of the binding
  Must output the transformed definition text, or $null to skip.

.PARAMETER Reverse
  (transform mode) Process definitions last-to-first. Default: $true.
  This is optimal for IDE caching (prefix stays cached).

.PARAMETER DryRun
  (transform mode) Print what would change without writing/verifying.

.PARAMETER LogFile
  (transform mode) Path to write a log of results.

.PARAMETER WarmupTimeout
  (transform mode) Seconds to wait for initial cache warmup. Default: 120.
#>
param(
    [Parameter(Mandatory=$true)]
    [string]$File,
    
    [Parameter(Mandatory=$true)]
    [ValidateSet("count","list","get","transform")]
    [string]$Mode,
    
    [int]$Index = -1,
    [string]$Name = "",
    [int]$From = 0,
    [int]$To = -1,
    [string]$Script = "",
    [switch]$Reverse = $true,
    [switch]$DryRun,
    [string]$LogFile = "",
    [int]$WarmupTimeout = 120
)

# ============================================================
# JSON ENCODING (handles Unicode properly for F* IDE)
# ============================================================

function ConvertTo-FstarJson {
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
# IDE SESSION MANAGEMENT
# ============================================================

function Start-FstarIde {
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
    
    # Drain stderr asynchronously to prevent buffer deadlock
    $proc.BeginErrorReadLine()
    
    # Read protocol-info line
    $proto = $proc.StandardOutput.ReadLine()
    if (-not ($proto -match '"protocol-info"')) {
        throw "Failed to start F* IDE: $proto"
    }
    
    return $proc
}

function Send-FstarCommand {
    param([System.Diagnostics.Process]$Proc, [string]$Json)
    $bytes = [System.Text.Encoding]::UTF8.GetBytes($Json + "`n")
    $Proc.StandardInput.BaseStream.Write($bytes, 0, $bytes.Length)
    $Proc.StandardInput.BaseStream.Flush()
}

function Send-FullBuffer {
    param([System.Diagnostics.Process]$Proc, [string]$Code, [string]$QueryId)
    $escaped = ConvertTo-FstarJson $Code
    $cmd = '{"query-id":"' + $QueryId + '","query":"full-buffer","args":{"kind":"full","code":' + $escaped + ',"with-symbols":false}}'
    Send-FstarCommand $Proc $cmd
}

function Wait-FullBufferResult {
    param(
        [System.Diagnostics.Process]$Proc,
        [int]$TimeoutSeconds = 300
    )
    
    $startedCount = 0
    $okCount = 0
    $failCount = 0
    $firstStartLine = -1
    $failLine = -1
    $failMessage = ""
    $finished = $false
    
    # Sync ReadLine: F* IDE produces output regularly during full-buffer.
    # If the process dies, ReadLine returns null.
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    
    while (-not $finished -and $sw.ElapsedMilliseconds -lt ($TimeoutSeconds * 1000)) {
        if ($Proc.HasExited) { break }
        
        $line = $Proc.StandardOutput.ReadLine()
        if ($null -eq $line) { break }
        
        if ($line -match '"full-buffer-fragment-started"') {
            $startedCount++
            if ($firstStartLine -eq -1) {
                try {
                    $parsed = $line | ConvertFrom-Json
                    $firstStartLine = $parsed.contents.ranges.beg[0]
                } catch {}
            }
        }
        elseif ($line -match '"full-buffer-fragment-ok"') {
            $okCount++
        }
        elseif ($line -match '"full-buffer-fragment-failed"') {
            $failCount++
            try {
                $parsed = $line | ConvertFrom-Json
                $failLine = $parsed.contents.ranges.beg[0]
            } catch {}
        }
        elseif ($line -match '"status":"failure"') {
            $failCount++
            try {
                $parsed = $line | ConvertFrom-Json
                if ($parsed.response) {
                    $failMessage = ($parsed.response | ForEach-Object { $_.message }) -join "; "
                }
            } catch {}
        }
        elseif ($line -match '"full-buffer-finished"') {
            $finished = $true
        }
    }
    
    return @{
        Started     = $startedCount
        OK          = $okCount
        Failed      = $failCount
        FirstLine   = $firstStartLine
        FailLine    = $failLine
        FailMessage = $failMessage
        Elapsed     = $sw.Elapsed
        Finished    = $finished
    }
}

function Stop-FstarIde {
    param([System.Diagnostics.Process]$Proc)
    try {
        Send-FstarCommand $Proc '{"query-id":"exit","query":"exit","args":{}}'
        $Proc.WaitForExit(5000)
    } catch {}
    if (-not $Proc.HasExited) {
        $Proc.Kill()
    }
}

function Send-Segment {
    param([System.Diagnostics.Process]$Proc, [string]$Code, [string]$QueryId)
    $escaped = ConvertTo-FstarJson $Code
    $cmd = '{"query-id":"' + $QueryId + '","query":"segment","args":{"kind":"full","code":' + $escaped + '}}'
    Send-FstarCommand $Proc $cmd
}

function Wait-SegmentResult {
    param([System.Diagnostics.Process]$Proc, [int]$TimeoutSeconds = 30)
    
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    while ($sw.ElapsedMilliseconds -lt ($TimeoutSeconds * 1000)) {
        if ($Proc.HasExited) { break }
        $line = $Proc.StandardOutput.ReadLine()
        if ($null -eq $line) { break }
        if ($line -match '"query-id"\s*:\s*"seg-') {
            try {
                $parsed = $line | ConvertFrom-Json
                if ($parsed.status -eq "success" -and $parsed.response -and $parsed.response.decls) {
                    return $parsed.response.decls.Count
                }
            } catch {}
            return -1
        }
    }
    return -1
}

# ============================================================
# PARSER: Split file into definitions  
# ============================================================

function Split-FstarDefinitions {
    param([string]$FilePath)
    
    $lines = [System.IO.File]::ReadAllLines($FilePath)
    $defs = @()
    
    $i = 0
    $total = $lines.Count
    $pushStart = -1
    
    while ($i -lt $total) {
        $line = $lines[$i]
        
        if ($line -match '^\s*#push-options') {
            $pushStart = $i
            $i++
            continue
        }
        
        if ($line -match '^(private\s+)?(unfold\s+)?(let\s+rec|let|type|val|instance|class)\s+(\S+)') {
            $defName = $Matches[4]
            $defName = $defName -replace '[({#].*', ''
            
            $startLine = if ($pushStart -ge 0) { $pushStart } else { $i }
            $endLine = $i + 1
            
            if ($pushStart -ge 0) {
                $depth = 1
                while ($endLine -lt $total -and $depth -gt 0) {
                    if ($lines[$endLine] -match '^\s*#push-options') { $depth++ }
                    if ($lines[$endLine] -match '^\s*#pop-options') { $depth-- }
                    $endLine++
                }
                $pushStart = -1
            } else {
                while ($endLine -lt $total) {
                    $nextLine = $lines[$endLine]
                    if ($nextLine -match '^\s*#push-options') { break }
                    if ($nextLine -match '^(private\s+)?(unfold\s+)?(let\s+rec|let|type|val|instance|class)\s+') { break }
                    if ($nextLine -match '^\(\*\s*-{20,}' -and $endLine -gt ($i + 1)) { break }
                    $endLine++
                }
            }
            
            # Trim trailing blanks but keep one separator
            while ($endLine -gt $startLine -and $lines[$endLine - 1].Trim() -eq '') {
                $endLine--
            }
            
            $text = ($lines[$startLine..($endLine-1)]) -join "`r`n"
            
            $defs += @{
                StartLine = $startLine
                EndLine   = $endLine
                Name      = $defName
                Text      = $text
            }
            
            $i = $endLine
            $pushStart = -1
        } else {
            $i++
        }
    }
    
    return $defs
}

# ============================================================
# MAIN
# ============================================================

$fullPath = (Resolve-Path $File -ErrorAction Stop).Path
$workDir = [System.IO.Path]::GetDirectoryName($fullPath)

switch ($Mode) {
    "count" {
        $defs = Split-FstarDefinitions $fullPath
        Write-Output "$($defs.Count) definitions"
    }
    
    "list" {
        $defs = Split-FstarDefinitions $fullPath
        for ($idx = 0; $idx -lt $defs.Count; $idx++) {
            $d = $defs[$idx]
            $firstMeaningful = ($d.Text -split "`r?`n" | Where-Object { 
                $_ -notmatch '^\s*#push-options' -and $_.Trim() -ne '' -and
                $_ -notmatch '^\s*\(\*' 
            } | Select-Object -First 1)
            if (-not $firstMeaningful) { $firstMeaningful = "(empty)" }
            $lineRange = "L$($d.StartLine+1)-$($d.EndLine)"
            Write-Output ("{0,3}: {1,-45} {2}" -f $idx, $d.Name, $lineRange)
        }
    }
    
    "get" {
        $defs = Split-FstarDefinitions $fullPath
        $target = $null
        
        if ($Index -ge 0) {
            if ($Index -ge $defs.Count) {
                Write-Error "Index $Index out of range (0..$($defs.Count-1))"
                exit 1
            }
            $target = $defs[$Index]
        } elseif ($Name -ne "") {
            $target = $defs | Where-Object { $_.Name -eq $Name } | Select-Object -First 1
            if (-not $target) {
                Write-Error "Definition '$Name' not found"
                exit 1
            }
        } else {
            Write-Error "Specify -Index or -Name"
            exit 1
        }
        
        Write-Output "# Definition: $($target.Name) (lines $($target.StartLine+1)-$($target.EndLine))"
        Write-Output $target.Text
    }
    
    "transform" {
        if (-not $Script) {
            Write-Error "-Script is required for transform mode"
            exit 1
        }
        $scriptPath = Resolve-Path $Script -ErrorAction Stop
        
        $defs = Split-FstarDefinitions $fullPath
        $defCountBefore = $defs.Count
        $lineCountBefore = (Get-Content $fullPath).Count
        if ($To -lt 0) { $To = $defs.Count }
        $To = [Math]::Min($To, $defs.Count)
        
        Write-Host "=== F* IDE Refactoring ===" -ForegroundColor Cyan
        Write-Host "File:    $File"
        Write-Host "Script:  $scriptPath"
        Write-Host "Range:   [$From, $To) of $($defs.Count) definitions"
        Write-Host "Defs:    $defCountBefore (pre-transform count, will verify post-transform)"
        Write-Host "Order:   $(if ($Reverse) { 'last-to-first (optimal)' } else { 'first-to-last' })"
        Write-Host ""
        
        if ($DryRun) {
            Write-Host "(DRY RUN - no verification)" -ForegroundColor Yellow
            Write-Host ""
        }
        
        # Build the iteration order
        $indices = $From..($To - 1)
        if ($Reverse) { [Array]::Reverse($indices) }
        
        $log = @()
        $changedCount = 0
        $failedCount = 0
        $skippedCount = 0
        
        # Start IDE session (if not dry-run)
        $ideProc = $null
        $fstarDefCountBefore = -1
        $fstarDefCount = -1
        if (-not $DryRun) {
            Write-Host "Starting F* IDE session..." -NoNewline
            $ideProc = Start-FstarIde $fullPath $workDir
            Write-Host " OK" -ForegroundColor Green
            
            # Warm the cache with the current file
            Write-Host "Warming cache (full file)..." -NoNewline
            $content = [System.IO.File]::ReadAllText($fullPath)
            $warmCode = $content.Replace("`r`n", "`n")
            Send-FullBuffer $ideProc $warmCode "warm"
            $warmResult = Wait-FullBufferResult $ideProc -TimeoutSeconds $WarmupTimeout
            
            if ($warmResult.Failed -gt 0) {
                Write-Host " FAILED" -ForegroundColor Red
                Write-Host "File does not verify clean! Fix errors first."
                Stop-FstarIde $ideProc
                exit 1
            }
            Write-Host " OK ($($warmResult.OK) frags, $($warmResult.Elapsed.TotalSeconds.ToString('F1'))s)" -ForegroundColor Green
            
            # Get F*'s own parse count for safety comparison
            Send-Segment $ideProc $warmCode "seg-pre"
            $fstarDefCountBefore = Wait-SegmentResult $ideProc -TimeoutSeconds 30
            Write-Host ""
        }
        
        try {
            foreach ($idx in $indices) {
                $d = $defs[$idx]
                $defText = $d.Text
                $defName = $d.Name
                
                Write-Host -NoNewline ("  [{0,3}] {1,-40} " -f $idx, $defName)
                
                # Invoke the transform script
                $transformed = & $scriptPath -Definition $defText -Index $idx -Name $defName
                
                if (-not $transformed -or $transformed -eq $defText) {
                    Write-Host "skip" -ForegroundColor DarkGray
                    $log += "$idx`t$defName`tskip"
                    $skippedCount++
                    continue
                }
                
                $transformedText = if ($transformed -is [array]) { 
                    $transformed -join "`r`n" 
                } else { 
                    $transformed 
                }
                
                # Check if actually different
                if ($transformedText -eq $defText) {
                    Write-Host "skip" -ForegroundColor DarkGray
                    $log += "$idx`t$defName`tskip"
                    $skippedCount++
                    continue
                }
                
                if ($DryRun) {
                    Write-Host "would change" -ForegroundColor Yellow
                    $log += "$idx`t$defName`tdry-run"
                    $changedCount++
                    continue
                }
                
                # Apply the transform to the file
                $rawText = [System.IO.File]::ReadAllText($fullPath)
                
                # Normalize line endings for search
                $searchText = $defText -replace "`n", "`r`n"
                $searchText = $searchText -replace "`r`r`n", "`r`n"
                $replaceText = $transformedText -replace "`n", "`r`n"
                $replaceText = $replaceText -replace "`r`r`n", "`r`n"
                
                $pos = $rawText.IndexOf($searchText)
                if ($pos -lt 0) {
                    $searchText = $defText
                    $pos = $rawText.IndexOf($searchText)
                }
                
                if ($pos -lt 0) {
                    Write-Host "not found" -ForegroundColor DarkYellow
                    $log += "$idx`t$defName`tnot-found"
                    $skippedCount++
                    continue
                }
                
                $newRawText = $rawText.Substring(0, $pos) + $replaceText + $rawText.Substring($pos + $searchText.Length)
                
                # Verify with IDE (send modified buffer WITHOUT writing file)
                $verifyCode = $newRawText.Replace("`r`n", "`n")
                $sw = [System.Diagnostics.Stopwatch]::StartNew()
                Send-FullBuffer $ideProc $verifyCode "t$idx"
                $result = Wait-FullBufferResult $ideProc -TimeoutSeconds 120
                
                if ($result.Failed -eq 0) {
                    # Write the file (verified OK)
                    [System.IO.File]::WriteAllText($fullPath, $newRawText)
                    Write-Host ("OK ({0:F1}s, {1} rechecked)" -f $sw.Elapsed.TotalSeconds, $result.Started) -ForegroundColor Green
                    $log += "$idx`t$defName`tok`t$($sw.Elapsed.TotalSeconds.ToString('F1'))s"
                    $changedCount++
                    # Re-parse definitions
                    $defs = Split-FstarDefinitions $fullPath
                } else {
                    # Rollback: re-send original buffer to restore IDE cache
                    $origCode = $rawText.Replace("`r`n", "`n")
                    Send-FullBuffer $ideProc $origCode "rb$idx"
                    $null = Wait-FullBufferResult $ideProc -TimeoutSeconds 120
                    
                    $failMsg = if ($result.FailLine -gt 0) { " (fail@L$($result.FailLine))" } else { "" }
                    Write-Host ("FAIL$failMsg ({0:F1}s)" -f $sw.Elapsed.TotalSeconds) -ForegroundColor Red
                    $log += "$idx`t$defName`tfail`t$($sw.Elapsed.TotalSeconds.ToString('F1'))s"
                    $failedCount++
                }
            }
            
            # F* segment parse check (while IDE is still alive)
            if ($ideProc -and -not $ideProc.HasExited) {
                $finalCode = [System.IO.File]::ReadAllText($fullPath).Replace("`r`n", "`n")
                Send-Segment $ideProc $finalCode "seg-final"
                $fstarDefCount = Wait-SegmentResult $ideProc -TimeoutSeconds 30
            }
        }
        finally {
            if ($ideProc) {
                Stop-FstarIde $ideProc
            }
        }
        
        Write-Host ""
        Write-Host "=== Results ===" -ForegroundColor Cyan
        Write-Host "  Changed:  $changedCount" -ForegroundColor Green
        Write-Host "  Failed:   $failedCount" -ForegroundColor $(if ($failedCount -gt 0) { "Red" } else { "DarkGray" })
        Write-Host "  Skipped:  $skippedCount" -ForegroundColor DarkGray
        
        # SAFETY CHECK: definition count must be preserved
        $defsAfter = Split-FstarDefinitions $fullPath
        $defCountAfter = $defsAfter.Count
        $lineCountAfter = (Get-Content $fullPath).Count
        # CRLF check
        $bytes = [System.IO.File]::ReadAllBytes($fullPath)
        $loneLF = 0
        for ($bi = 0; $bi -lt $bytes.Length; $bi++) {
            if ($bytes[$bi] -eq 10 -and ($bi -eq 0 -or $bytes[$bi-1] -ne 13)) { $loneLF++ }
        }
        
        $failed = $false
        if ($defCountAfter -ne $defCountBefore) {
            Write-Host ""
            Write-Host "!!! SAFETY CHECK FAILED !!!" -ForegroundColor Red -BackgroundColor DarkRed
            Write-Host "  Definition count BEFORE: $defCountBefore" -ForegroundColor Red
            Write-Host "  Definition count AFTER:  $defCountAfter" -ForegroundColor Red
            Write-Host "  FILE MAY BE CORRUPTED — review immediately!" -ForegroundColor Red
            $failed = $true
        }
        if ($loneLF -gt 0) {
            Write-Host "!!! CRLF SAFETY CHECK FAILED !!!" -ForegroundColor Red -BackgroundColor DarkRed
            Write-Host "  Lone LF bytes found: $loneLF" -ForegroundColor Red
            $failed = $true
        }
        if ($fstarDefCount -eq -1 -and $changedCount -gt 0) {
            Write-Host "!!! F* PARSE CHECK FAILED !!!" -ForegroundColor Red -BackgroundColor DarkRed
            Write-Host "  F* could not parse the final file (segment returned no decls)" -ForegroundColor Red
            $failed = $true
        } elseif ($fstarDefCount -gt 0 -and $fstarDefCountBefore -gt 0 -and $fstarDefCount -ne $fstarDefCountBefore) {
            Write-Host "!!! F* PARSE STRUCTURE CHANGED !!!" -ForegroundColor Red -BackgroundColor DarkRed
            Write-Host "  F* segment BEFORE: $fstarDefCountBefore decls" -ForegroundColor Red
            Write-Host "  F* segment AFTER:  $fstarDefCount decls" -ForegroundColor Red
            $failed = $true
        }
        if (-not $failed) {
            $segInfo = if ($fstarDefCount -gt 0) { ", F* parse OK ($fstarDefCount decls)" } else { "" }
            Write-Host "  Safety:   $defCountAfter defs (unchanged), $lineCountAfter lines (was $lineCountBefore), CRLF OK$segInfo" -ForegroundColor Green
        }
        !$failed
        
        if ($LogFile) {
            $log | Out-File -FilePath $LogFile -Encoding UTF8
            Write-Host "Log: $LogFile"
        }
    }
}
