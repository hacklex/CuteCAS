#!/usr/bin/env pwsh
# build-all.ps1 — verify the entire CuteCAS Core.* tower in dependency order.
#
# Regenerated 2026-06-01. Order derived from `fstar.exe --dep full` and a
# topological sort over the .checked dependency graph (.fsti precedes .fst;
# implementations depend only on dependencies' interfaces).
#
# Resource rules (.github/copilot-instructions.md §3): SEQUENTIAL, one module
# at a time, default limits, always cache to obj/. Do NOT parallelize.
#
# Usage:
#   .\build-all.ps1            # stop at first failure
#   .\build-all.ps1 -KeepGoing # verify all, collect every failure
#   .\build-all.ps1 -Clean     # ignore cache (force full re-check)

param(
  [switch]$KeepGoing,
  [switch]$Clean
)

$ErrorActionPreference = 'Stop'
$root   = $PSScriptRoot
$fstar  = 'C:\FStar\bin\fstar.exe'
$objdir = Join-Path $root 'obj'

$modules = @(
  'Core.Algebra.fst',
  'Core.Permutation.fsti',
  'Core.Algebra.Int.fst',
  'Core.Algebra.Notation.fst',
  'Core.Algebra.Combinators.fst',
  'Core.Algebra.Helpers.fst',
  'Core.Tactics.CanonRing.fst',
  'Core.Algebra.Divisibility.fst',
  'Core.Algebra.NotationTest.fst',
  'Core.Algebra.Test.fst',
  'Core.Polynomial.fst',
  'Core.AlgebraicConstant.fsti',
  'Core.Polynomial.Div.fsti',
  'Core.Polynomial.Unique.fsti',
  'Core.AlgebraicConstant.fst',
  'Core.Derivation.fsti',
  'Core.Polynomial.Derivative.fsti',
  'Core.Derivation.fst',
  'Core.FinSum.fsti',
  'Core.FinSum.fst',
  'Core.Fractions.fsti',
  'Core.Fractions.fst',
  'Core.Vector.fsti',
  'Core.Matrix.fsti',
  'Core.Permutation.Enum.fsti',
  'Core.Permutation.Sum.fsti',
  'Core.Matrix.Determinant.fsti',
  'Core.Matrix.Ring.fst',
  'Core.Matrix.Adjugate.fst',
  'Core.Matrix.MultiDistrib.fst',
  'Core.Matrix.Determinant.Mul.fsti',
  'Core.Matrix.NullVec.fst',
  'Core.Matrix.Sylvester.fst',
  'Core.Polynomial.GCD.fsti',
  'Core.Polynomial.SquareFree.fst',
  'Core.Polynomial.Coeff.fsti',
  'Core.Matrix.Resultant.fst',
  'Core.Risch.LRT.fst',
  'Core.Polynomial.Irreducible.fst',
  'Core.Polynomial.PPInvariant.fst',
  'Core.Polynomial.Factorization.fst',
  'Core.Tactics.CanonCommGroup.fst',
  'Core.Vector.fst',
  'Core.Matrix.KernelDet.fst',
  'Core.Polynomial.Tests.fst',
  'Core.Polynomial.GCD.fst',
  'Core.Polynomial.PartialFraction.fst',
  'Core.Permutation.fst',
  'Core.Risch.Hermite.fst',
  'Core.Polynomial.Coeff.fst',
  'Core.Matrix.Determinant.Mul.fst',
  'Core.Risch.Rational.fst',
  'Core.Polynomial.Div.fst',
  'Core.Polynomial.Unique.fst',
  'Core.Polynomial.Derivative.fst',
  'Core.RationalDeriv.fst',
  'Core.Permutation.Sum.fst',
  'Core.Permutation.Enum.fst',
  'Core.Matrix.fst',
  'Core.Matrix.Determinant.fst'
)

if ($Clean) {
  Write-Host "Clean build: NOT wiping obj/ (cache is never wiped wholesale per repo rules)." -ForegroundColor Yellow
  Write-Host "If you truly need a cold rebuild, invalidate targeted .checked files by hand." -ForegroundColor Yellow
}

$flags = @('--include', $root, '--cache_checked_modules', '--cache_dir', $objdir)
$failed = @()
$i = 0
$sw = [System.Diagnostics.Stopwatch]::StartNew()
foreach ($m in $modules) {
  $i++
  $path = Join-Path $root $m
  if (-not (Test-Path $path)) { Write-Host "[$i/$($modules.Count)] SKIP (missing): $m" -ForegroundColor DarkGray; continue }
  Write-Host ("[{0}/{1}] {2}" -f $i, $modules.Count, $m) -NoNewline
  $t0 = $sw.Elapsed.TotalSeconds
  & $fstar @flags $path 2>&1 | Out-String -OutVariable out | Out-Null
  $dt = [math]::Round($sw.Elapsed.TotalSeconds - $t0, 1)
  if ($LASTEXITCODE -ne 0) {
    Write-Host "  FAIL (${dt}s)" -ForegroundColor Red
    $failed += $m
    $out -split "`n" | Select-Object -First 25 | ForEach-Object { Write-Host "    $_" -ForegroundColor Red }
    if (-not $KeepGoing) { break }
  } else {
    Write-Host "  ok (${dt}s)" -ForegroundColor Green
  }
}
$sw.Stop()
Write-Host ""
if ($failed.Count -eq 0) {
  Write-Host ("ALL GREEN: {0} modules verified in {1}s." -f $modules.Count, [math]::Round($sw.Elapsed.TotalSeconds,1)) -ForegroundColor Green
  exit 0
} else {
  Write-Host ("FAILURES ({0}): {1}" -f $failed.Count, ($failed -join ', ')) -ForegroundColor Red
  exit 1
}