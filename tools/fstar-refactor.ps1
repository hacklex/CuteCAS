<#
.SYNOPSIS
  F* definition-level refactoring framework.
  
  Splits an F* source file into numbered definitions, allows targeted
  transforms on individual definitions, and verifies the result with
  fstar.exe before committing.

.DESCRIPTION
  Modes:
    -Mode count     : Print number of definitions in the file.
    -Mode list      : Print index + first line of each definition.
    -Mode get       : Print definition by -Index or -Name.
    -Mode transform : Apply -Script to definitions in range [-From, -To).
                      Verifies after each edit; rolls back on failure.

  A "definition" is a top-level binding: `let`, `let rec`, `private let`,
  `type`, `instance`, `class`, `val`, etc.  Optionally wrapped in a
  `#push-options` / `#pop-options` block (included in the definition).

.PARAMETER File
  Path to the .fst or .fsti file to operate on.

.PARAMETER Mode
  One of: count, list, get, transform.

.PARAMETER Index
  (get mode) 0-based index of the definition to retrieve.

.PARAMETER Name
  (get mode) Name of the definition to retrieve (first match).

.PARAMETER From
  (transform mode) Start index (inclusive). Default: 0.

.PARAMETER To
  (transform mode) End index (exclusive). Default: definition count.

.PARAMETER Script
  (transform mode) Path to a PowerShell script that transforms a single
  definition. The script receives:
    $Definition  - string content of the definition (may be multi-line)
    $Index       - 0-based definition number
    $Name        - name of the binding (e.g. "prod_range_zero_factor")
  It must output the transformed definition text (stdout), or $null / empty
  to skip (leave unchanged).

.PARAMETER FstarArgs
  (transform mode) Extra arguments to fstar.exe. Default:
  "--cache_checked_modules --cache_dir obj"

.PARAMETER DryRun
  (transform mode) If set, print what would change without writing.

.PARAMETER LogFile
  (transform mode) Path to write a log of results per definition.

.EXAMPLE
  # Count definitions
  .\fstar-refactor.ps1 -File Core.Matrix.Determinant.fst -Mode count

  # List all definitions
  .\fstar-refactor.ps1 -File Core.Matrix.Determinant.fst -Mode list

  # Get definition #5
  .\fstar-refactor.ps1 -File Core.Matrix.Determinant.fst -Mode get -Index 5

  # Get definition by name
  .\fstar-refactor.ps1 -File Core.Matrix.Determinant.fst -Mode get -Name "det_transpose"

  # Apply a transform script to definitions 10-20
  .\fstar-refactor.ps1 -File Core.Matrix.Determinant.fst -Mode transform `
    -Script .\transforms\drop-fin-casts.ps1 -From 10 -To 20

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
    [string]$FstarArgs = "--cache_checked_modules --cache_dir obj",
    [switch]$DryRun,
    [string]$LogFile = ""
)

# ============================================================
# PARSER: Split file into definitions
# ============================================================

function Split-FstarDefinitions {
    param([string]$FilePath)
    
    $lines = [System.IO.File]::ReadAllLines($FilePath)
    $defs = @()  # list of @{StartLine; EndLine; Name; Text}
    
    $i = 0
    $total = $lines.Count
    
    # Track whether we're inside a #push-options block
    $pushStart = -1
    
    while ($i -lt $total) {
        $line = $lines[$i]
        
        # Detect #push-options (start of a possible definition block)
        if ($line -match '^\s*#push-options') {
            $pushStart = $i
            $i++
            continue
        }
        
        # Detect top-level definition start
        # Matches: let, let rec, private let, private let rec, type, val, instance, class
        if ($line -match '^(private\s+)?(let\s+rec|let|type|val|instance|class)\s+(\S+)') {
            $defName = $Matches[3]
            # Clean up name (remove type params, etc.)
            $defName = $defName -replace '[({#].*', ''
            
            $startLine = if ($pushStart -ge 0) { $pushStart } else { $i }
            
            # Find end of definition:
            # - If we started with #push-options, find matching #pop-options
            # - Otherwise, find next top-level definition or #push-options
            $endLine = $i + 1
            
            if ($pushStart -ge 0) {
                # Find matching #pop-options
                $depth = 1
                while ($endLine -lt $total -and $depth -gt 0) {
                    if ($lines[$endLine] -match '^\s*#push-options') { $depth++ }
                    if ($lines[$endLine] -match '^\s*#pop-options') { $depth-- }
                    $endLine++
                }
                $pushStart = -1
            } else {
                # Find next definition boundary
                while ($endLine -lt $total) {
                    $nextLine = $lines[$endLine]
                    if ($nextLine -match '^\s*#push-options') { break }
                    if ($nextLine -match '^(private\s+)?(let\s+rec|let|type|val|instance|class)\s+') { break }
                    # Also stop at section comments (long ===== or ----- separators)
                    if ($nextLine -match '^(\(\*\s*={10,}|/\*\s*={10,})' -and $endLine -gt ($i + 1)) { break }
                    $endLine++
                }
            }
            
            # Trim trailing blank lines from this definition
            while ($endLine -gt $startLine -and $lines[$endLine - 1].Trim() -eq '') {
                $endLine--
            }
            # But keep one trailing blank for separation
            if ($endLine -lt $total -and $lines[$endLine].Trim() -eq '') {
                $endLine++
            }
            
            $text = ($lines[$startLine..($endLine-1)]) -join "`r`n"
            
            $defs += @{
                StartLine = $startLine
                EndLine   = $endLine  # exclusive
                Name      = $defName
                Text      = $text
            }
            
            $i = $endLine
            $pushStart = -1
        } else {
            # Not a definition line — skip
            # But reset pushStart if we hit something that isn't a definition
            # after a #push-options (comments between push and let are ok)
            if ($pushStart -ge 0 -and $line.Trim() -ne '' -and 
                $line -notmatch '^\s*(\(\*.*\*\)|\(\*|.*\*\))$' -and
                $line -notmatch '^\s*//') {
                # Non-comment, non-empty line after #push without a def — weird.
                # Just keep scanning.
            }
            $i++
        }
    }
    
    return $defs
}

# ============================================================
# MAIN
# ============================================================

$fullPath = Resolve-Path $File -ErrorAction Stop

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
        if ($To -lt 0) { $To = $defs.Count }
        $To = [Math]::Min($To, $defs.Count)
        
        Write-Output "Transforming definitions [$From, $To) in $File"
        Write-Output "Using script: $scriptPath"
        Write-Output "Total definitions: $($defs.Count)"
        Write-Output ""
        
        $log = @()
        $changedCount = 0
        $failedCount = 0
        $skippedCount = 0
        
        for ($idx = $From; $idx -lt $To; $idx++) {
            $d = $defs[$idx]
            $defText = $d.Text
            $defName = $d.Name
            
            Write-Host -NoNewline "  [$idx] $defName... "
            
            # Invoke the transform script
            $transformed = & $scriptPath -Definition $defText -Index $idx -Name $defName
            
            if (-not $transformed -or $transformed -eq $defText) {
                Write-Host "skip (unchanged)"
                $log += "$idx`t$defName`tskip"
                $skippedCount++
                continue
            }
            
            $transformedText = if ($transformed -is [array]) { 
                $transformed -join "`r`n" 
            } else { 
                $transformed 
            }
            
            if ($DryRun) {
                Write-Host "would change"
                Write-Output "--- BEFORE ---"
                Write-Output $defText
                Write-Output "--- AFTER ---"
                Write-Output $transformedText
                Write-Output ""
                $log += "$idx`t$defName`tdry-run"
                continue
            }
            
            # Read the current file as raw text (preserves exact CRLF)
            $rawText = [System.IO.File]::ReadAllText($fullPath)
            
            # Backup current state
            $backupPath = "$fullPath.refactor-bak"
            [System.IO.File]::WriteAllText($backupPath, $rawText)
            
            # Replace the definition text in the raw file
            # The definition text uses `n from the parser; normalize to match raw CRLF
            $searchText = $defText -replace "`n", "`r`n"
            $searchText = $searchText -replace "`r`r`n", "`r`n"  # avoid double-CR
            $replaceText = $transformedText -replace "`n", "`r`n"
            $replaceText = $replaceText -replace "`r`r`n", "`r`n"
            
            # Find and replace (first occurrence)
            $pos = $rawText.IndexOf($searchText)
            if ($pos -lt 0) {
                # Fallback: try with just LF
                $searchText = $defText
                $pos = $rawText.IndexOf($searchText)
            }
            
            if ($pos -lt 0) {
                Write-Host "skip (text not found in file)"
                $log += "$idx`t$defName`tnot-found"
                $skippedCount++
                Remove-Item $backupPath -ErrorAction SilentlyContinue
                continue
            }
            
            $newRawText = $rawText.Substring(0, $pos) + $replaceText + $rawText.Substring($pos + $searchText.Length)
            
            # Write the transformed file
            [System.IO.File]::WriteAllText($fullPath, $newRawText)
            
            # Verify with fstar.exe
            $fstarDir = [System.IO.Path]::GetDirectoryName($fullPath)
            $fileName = [System.IO.Path]::GetFileName($fullPath)
            
            $proc = Start-Process -FilePath "fstar.exe" `
                -ArgumentList "$fileName $FstarArgs" `
                -WorkingDirectory $fstarDir `
                -NoNewWindow -Wait -PassThru `
                -RedirectStandardOutput "$fstarDir\fstar-refactor-stdout.tmp" `
                -RedirectStandardError "$fstarDir\fstar-refactor-stderr.tmp" 2>$null
            
            $stdout = Get-Content "$fstarDir\fstar-refactor-stdout.tmp" -Raw -ErrorAction SilentlyContinue
            $stderr = Get-Content "$fstarDir\fstar-refactor-stderr.tmp" -Raw -ErrorAction SilentlyContinue
            $output = "$stdout`n$stderr"
            Remove-Item "$fstarDir\fstar-refactor-stdout.tmp" -ErrorAction SilentlyContinue
            Remove-Item "$fstarDir\fstar-refactor-stderr.tmp" -ErrorAction SilentlyContinue
            
            if ($proc.ExitCode -eq 0 -and $output -match 'All verification conditions discharged successfully') {
                Write-Host "OK (changed)"
                $log += "$idx`t$defName`tok"
                $changedCount++
                # Re-parse definitions since content changed
                $defs = Split-FstarDefinitions $fullPath
                if ($To -gt $defs.Count) { $To = $defs.Count }
                Remove-Item $backupPath -ErrorAction SilentlyContinue
            } else {
                Write-Host "FAIL (rolled back)"
                # Restore backup
                [System.IO.File]::WriteAllText($fullPath, $rawText)
                $log += "$idx`t$defName`tfail"
                $failedCount++
                Remove-Item $backupPath -ErrorAction SilentlyContinue
            }
        }
        
        Write-Output ""
        Write-Output "Results: $changedCount changed, $failedCount failed, $skippedCount skipped"
        
        if ($LogFile) {
            $log | Out-File -FilePath $LogFile -Encoding UTF8
            Write-Output "Log written to: $LogFile"
        }
    }
}
