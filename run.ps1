param([Parameter(ValueFromRemainingArguments=$true)][string[]]$FArgs)
$ErrorActionPreference = 'Stop'

Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;
public static class Job {
    [DllImport("kernel32", SetLastError=true)] public static extern IntPtr CreateJobObject(IntPtr a, string n);
    [DllImport("kernel32", SetLastError=true)] public static extern bool SetInformationJobObject(IntPtr j, int c, IntPtr i, uint l);
    [DllImport("kernel32", SetLastError=true)] public static extern bool AssignProcessToJobObject(IntPtr j, IntPtr p);
    [DllImport("kernel32", SetLastError=true)] public static extern bool CloseHandle(IntPtr h);
}
"@

$j = [Job]::CreateJobObject([IntPtr]::Zero, $null)
if ($j -eq [IntPtr]::Zero) { throw "CreateJobObject failed" }

$JOB_OBJECT_LIMIT_PROCESS_MEMORY = 0x100
$JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE = 0x2000
$flags = $JOB_OBJECT_LIMIT_PROCESS_MEMORY -bor $JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE

$info = New-Object byte[] 144
[Array]::Copy([BitConverter]::GetBytes([int]$flags), 0, $info, 16, 4)
[Array]::Copy([BitConverter]::GetBytes([uint64]4GB), 0, $info, 112, 8)
$ptr = [System.Runtime.InteropServices.Marshal]::AllocHGlobal(144)
try {
    [System.Runtime.InteropServices.Marshal]::Copy($info, 0, $ptr, 144)
    if (-not [Job]::SetInformationJobObject($j, 9, $ptr, 144)) {
        throw "Set ExtendedLimit failed: $([System.Runtime.InteropServices.Marshal]::GetLastWin32Error())"
    }
} finally { [System.Runtime.InteropServices.Marshal]::FreeHGlobal($ptr) }

$cpuInfo = New-Object byte[] 8
[Array]::Copy([BitConverter]::GetBytes([int](1 -bor 4)), 0, $cpuInfo, 0, 4)
[Array]::Copy([BitConverter]::GetBytes([int]5000), 0, $cpuInfo, 4, 4)
$ptr2 = [System.Runtime.InteropServices.Marshal]::AllocHGlobal(8)
try {
    [System.Runtime.InteropServices.Marshal]::Copy($cpuInfo, 0, $ptr2, 8)
    if (-not [Job]::SetInformationJobObject($j, 15, $ptr2, 8)) {
        Write-Warning "Set CpuRateControl failed: $([System.Runtime.InteropServices.Marshal]::GetLastWin32Error())"
    }
} finally { [System.Runtime.InteropServices.Marshal]::FreeHGlobal($ptr2) }

$psi = New-Object System.Diagnostics.ProcessStartInfo
$psi.FileName = 'fstar.exe'
foreach ($a in $FArgs) { $psi.ArgumentList.Add($a) | Out-Null }
$psi.UseShellExecute = $false
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.WorkingDirectory = (Get-Location).Path

$proc = [System.Diagnostics.Process]::Start($psi)
$assigned = [Job]::AssignProcessToJobObject($j, $proc.Handle)
if (-not $assigned) { Write-Warning "AssignProcessToJobObject failed: $([System.Runtime.InteropServices.Marshal]::GetLastWin32Error())" }

$outTask = $proc.StandardOutput.ReadToEndAsync()
$errTask = $proc.StandardError.ReadToEndAsync()

$peak = 0L
$myPid = $proc.Id
$cmd = Get-Command Stop-Process
$tick = 0
while (-not $proc.HasExited) {
    Start-Sleep -Milliseconds 500
    try { $ws = (Get-Process -Id $myPid -ErrorAction Stop).WorkingSet64 } catch { break }
    if ($ws -gt $peak) { $peak = $ws }
    if ($ws -gt 4.2GB) {
        Write-Host "[runfstar] Safety kill at $([math]::Round($ws/1GB,2)) GB"
        & $cmd -Id $myPid -Force
        break
    }
    $tick++
    if ($tick % 60 -eq 0) { Write-Host "[runfstar] running, RAM=$([math]::Round($ws/1MB)) MB peak=$([math]::Round($peak/1MB)) MB" }
}

$outTask.Wait() | Out-Null
$errTask.Wait() | Out-Null
if ($outTask.Result) { Write-Host $outTask.Result }
if ($errTask.Result) { Write-Host -ForegroundColor Yellow $errTask.Result }
Write-Host "[runfstar] ExitCode=$($proc.ExitCode) PeakRAM=$([math]::Round($peak/1MB)) MB"
[Job]::CloseHandle($j) | Out-Null
exit $proc.ExitCode
