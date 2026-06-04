param([string]$p)
$t = [IO.File]::ReadAllText($p)
$t = $t -replace "`r`n", "`n"
$t = $t -replace "`n", "`r`n"
[IO.File]::WriteAllText($p, $t)
$lines = [IO.File]::ReadAllText($p) -split "`r`n", 0
$lone = ([regex]::Matches([IO.File]::ReadAllText($p), "(?<!`r)`n")).Count
Write-Output "lone-LF: $lone"
