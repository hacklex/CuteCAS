# Deslop sweep driver: runs the 3 transforms over each module (dependency order),
# logs progress to tools\sweep.log (tail it to watch), checks def-count invariance,
# normalizes CRLF. The underlying framework verifies + rolls back per definition,
# so the build cannot be broken. Run: powershell tools\sweep-deslop.ps1
$ErrorActionPreference = 'Continue'
$root = 'C:\Projects\CuteCAS'
Set-Location $root
$log = Join-Path $root 'tools\sweep.log'
$refactor = Join-Path $root 'tools\fstar-refactor.ps1'
"== deslop sweep start $(Get-Date -Format o) ==" | Out-File $log

$transforms = @('drop-tc-solve-slop.ps1','drop-redundant-eq-laws.ps1','drop-poly-mul-comm.ps1')
$modules = @(
  'Core.Algebra.Helpers.fst','Core.Tactics.CanonRing.fst','Core.Algebra.Divisibility.fst',
  'Core.AlgebraicConstant.fst','Core.Derivation.fst','Core.FinSum.Convolution.fst','Core.FinSum.fst',
  'Core.Fractions.fst','Core.Polynomial.Coeff.fst','Core.Polynomial.Eval.fst','Core.Polynomial.Div.fst',
  'Core.Polynomial.Unique.fst','Core.Polynomial.GCD.fst','Core.Polynomial.SquareFree.fst',
  'Core.Polynomial.Irreducible.fst','Core.Polynomial.PPInvariant.fst','Core.Polynomial.Factorization.fst',
  'Core.Polynomial.Derivative.fst','Core.Polynomial.Root.fst','Core.Polynomial.Product.fst',
  'Core.Polynomial.Tests.fst','Core.AlgebraicConstant.Field.fst','Core.Permutation.Sum.fst',
  'Core.Matrix.MultiDistrib.fst','Core.Matrix.Adjugate.fst','Core.Matrix.NullVec.fst',
  'Core.Matrix.Sylvester.fst','Core.Matrix.Determinant.fst','Core.Matrix.Determinant.Mul.fst',
  'Core.Matrix.Triangular.fst','Core.Matrix.Resultant.fst','Core.Matrix.KernelDet.fst',
  'Core.Matrix.ResultantLinear.fst','Core.Matrix.ResultantMul.fst','Core.Matrix.ResultantPeel.fst',
  'Core.Matrix.ResultantPoisson.fst','Core.Risch.LRT.fst','Core.Risch.Hermite.fst',
  'Core.Risch.Rational.fst','Core.RationalDeriv.fst'
)

$grand = 0
foreach ($m in $modules) {
  if (-not (Test-Path (Join-Path $root $m))) { "SKIP missing $m" | Out-File $log -Append; continue }
  $cb = (& $refactor -File $m -Mode count) -join ' '
  $nb = [regex]::Match($cb,'(\d+)\s+definition').Groups[1].Value
  $tot = 0
  foreach ($tr in $transforms) {
    $out = (& $refactor -File $m -Mode transform -Script (Join-Path $root "tools\transforms\$tr") 2>&1) -join "`n"
    $res = [regex]::Match($out,'Results:.*').Value
    if ($res -match '(\d+) changed') { $tot += [int]$Matches[1] }
    "[$tr]`t$m`t$res" | Out-File $log -Append
  }
  $ca = (& $refactor -File $m -Mode count) -join ' '
  $na = [regex]::Match($ca,'(\d+)\s+definition').Groups[1].Value
  $inv = if ($nb -eq $na) { 'count-OK' } else { "COUNT-MISMATCH $nb->$na" }
  $p = Join-Path $root $m
  $t = [System.IO.File]::ReadAllText($p); $t = $t -replace "`r`n","`n" -replace "`n","`r`n"; [System.IO.File]::WriteAllText($p,$t)
  $grand += $tot
  "=== $m  changed=$tot  $inv  ($(Get-Date -Format HH:mm:ss)) ===" | Out-File $log -Append
}
"== deslop sweep complete: $grand defs changed, $(Get-Date -Format o) ==" | Out-File $log -Append
