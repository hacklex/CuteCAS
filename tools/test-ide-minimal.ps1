# Minimal F* IDE test
$psi = New-Object System.Diagnostics.ProcessStartInfo
$psi.FileName = "fstar.exe"
$psi.Arguments = "--ide --cache_checked_modules --cache_dir obj Core.Matrix.Determinant.fst"
$psi.UseShellExecute = $false
$psi.RedirectStandardInput = $true
$psi.RedirectStandardOutput = $true
$psi.RedirectStandardError = $true
$psi.WorkingDirectory = "c:\Projects\CuteCAS"

$proc = [System.Diagnostics.Process]::Start($psi)
$proc.BeginErrorReadLine()

$proto = $proc.StandardOutput.ReadLine()
Write-Host "Proto: OK"

# Build code
$content = [System.IO.File]::ReadAllText("c:\Projects\CuteCAS\Core.Matrix.Determinant.fst")
$code = $content.Replace("`r`n", "`n")
Write-Host "File: $($code.Length) chars"

# Escape
$sb = [System.Text.StringBuilder]::new($code.Length + 5000)
[void]$sb.Append('"')
foreach ($ch in $code.ToCharArray()) {
    switch ([int]$ch) {
        34  { [void]$sb.Append('\"') }
        92  { [void]$sb.Append('\\') }
        10  { [void]$sb.Append('\n') }
        13  { [void]$sb.Append('\r') }
        9   { [void]$sb.Append('\t') }
        default {
            if ([int]$ch -lt 32) { [void]$sb.Append(('\u{0:X4}' -f [int]$ch)) }
            elseif ([int]$ch -gt 127) { [void]$sb.Append(('\u{0:X4}' -f [int]$ch)) }
            else { [void]$sb.Append($ch) }
        }
    }
}
[void]$sb.Append('"')
$escaped = $sb.ToString()
Write-Host "Escaped: $($escaped.Length)"

$cmd = '{"query-id":"fb","query":"full-buffer","args":{"kind":"full","code":' + $escaped + ',"with-symbols":false}}'
$bytes = [System.Text.Encoding]::UTF8.GetBytes($cmd + "`n")
Write-Host "Sending $($bytes.Length) bytes..."
$proc.StandardInput.BaseStream.Write($bytes, 0, $bytes.Length)
$proc.StandardInput.BaseStream.Flush()

$sw = [System.Diagnostics.Stopwatch]::StartNew()
$okCount = 0
while ($true) {
    $line = $proc.StandardOutput.ReadLine()
    if ($null -eq $line) { Write-Host "EOF"; break }
    if ($line -match '"full-buffer-fragment-ok"') { $okCount++ }
    if ($line -match '"full-buffer-finished"') { Write-Host "DONE: $okCount OK in $($sw.Elapsed.TotalSeconds.ToString('F1'))s"; break }
}

$proc.StandardInput.WriteLine('{"query-id":"exit","query":"exit","args":{}}')
$proc.WaitForExit(5000)
if (!$proc.HasExited) { $proc.Kill() }