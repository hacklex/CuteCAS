param(
    [string]$File = "Core.Matrix.Determinant.fst",
    [string]$Mode = "full-buffer",  # "full-buffer" or "segment"
    [int]$UpToLine = 0  # 0 = entire file
)

$psi = New-Object System.Diagnostics.ProcessStartInfo
$psi.FileName = "fstar.exe"
$psi.Arguments = "--ide --cache_checked_modules --cache_dir obj $File"
$psi.UseShellExecute = $false
$psi.RedirectStandardInput = $true
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.WorkingDirectory = "c:\Projects\CuteCAS"

$proc = [System.Diagnostics.Process]::Start($psi)

# Read protocol-info
$protoLine = $proc.StandardOutput.ReadLine()
Write-Host "PROTO: $protoLine"

if ($Mode -eq "segment") {
    # Read file content  
    $content = [System.IO.File]::ReadAllText("c:\Projects\CuteCAS\$File")
    $escaped = ($content | ConvertTo-Json)
    $cmd = '{"query-id":"seg","query":"segment","args":{"code":' + $escaped + '}}'
    $proc.StandardInput.WriteLine($cmd)
    
    # Read response
    $resp = $proc.StandardOutput.ReadLine()
    Write-Host $resp
} elseif ($Mode -eq "full-buffer") {
    # Read file content (optionally up to a line)
    $lines = [System.IO.File]::ReadAllLines("c:\Projects\CuteCAS\$File")
    if ($UpToLine -gt 0 -and $UpToLine -lt $lines.Length) {
        $lines = $lines[0..($UpToLine-1)]
    }
    $content = ($lines -join "`n") + "`n"
    $escaped = ($content | ConvertTo-Json)
    $cmd = '{"query-id":"fb","query":"full-buffer","args":{"kind":"full","code":' + $escaped + ',"with-symbols":false}}'
    $proc.StandardInput.WriteLine($cmd)
    
    # Read responses until full-buffer-finished
    $sw = [System.Diagnostics.Stopwatch]::StartNew()
    $timeout = 300000  # 5 min
    while ($sw.ElapsedMilliseconds -lt $timeout) {
        $line = $proc.StandardOutput.ReadLine()
        if ($null -eq $line) { break }
        Write-Host $line
        if ($line -match "full-buffer-finished") { break }
        if ($line -match '"status":"failure"') { 
            Write-Host "FAILURE DETECTED"
            break 
        }
    }
    Write-Host "Elapsed: $($sw.Elapsed)"
}

# Exit
$proc.StandardInput.WriteLine('{"query-id":"exit","query":"exit","args":{}}')
$proc.WaitForExit(5000)
if (!$proc.HasExited) { $proc.Kill() }