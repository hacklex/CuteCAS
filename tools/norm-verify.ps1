param([string]$p)
$t=[System.IO.File]::ReadAllText($p); $t=$t -replace "`r`n","`n" -replace "`n","`r`n"; [System.IO.File]::WriteAllText($p,$t)
$lf = ([regex]::Matches($t, "(?<!`r)`n")).Count
Write-Host "LoneLF=$lf"
