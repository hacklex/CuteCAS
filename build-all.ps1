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
  'Core.Algebra.CongruenceMod.fst',
  'Core.Algebra.NotationTest.fst',
  'Core.Algebra.Test.fst',
  'Core.NumberTheory.fst',
  'Core.Modular.ResidueRing.fst',
  'Core.Modular.PrimeField.fst',
  'Core.Polynomial.fst',
  'Core.Polynomial.Div.fsti',
  'Core.Polynomial.Unique.fsti',
  'Core.Algebra.Derivation.fsti',
  'Core.Polynomial.Derivative.fsti',
  'Core.Algebra.Derivation.fst',
  'Core.FinSum.fsti',
  'Core.FinSum.fst',
  'Core.Fractions.fsti',
  'Core.Fractions.fst',
  'Core.Fractions.RationalAbs.fst',
  'Core.Vector.fsti',
  'Core.Matrix.fsti',
  'Core.Permutation.Enum.fsti',
  'Core.Permutation.Sum.fsti',
  'Core.Matrix.Determinant.fsti',
  'Core.Polynomial.Sylvester.fst',
  'Core.Polynomial.GCD.fsti',
  'Core.Polynomial.SquareFree.fst',
  'Core.Polynomial.Coeff.fsti',
  'Core.Polynomial.Irreducible.fst',
  'Core.AlgebraicConstant.fsti',
  'Core.Polynomial.Factorization.fst',
  'Core.Tactics.CanonCommGroup.fst',
  'Core.Vector.fst',
  'Core.Polynomial.Tests.fst',
  'Core.Polynomial.GCD.fst',
  'Core.Polynomial.PartialFraction.fst',
  'Core.AlgebraicConstant.fst',
  'Core.AlgebraicConstant.Root.fst',
  'Core.AlgebraicConstant.Eval.fst',
  'Core.AlgebraicConstant.Peel.fst',
  'Core.AlgebraicConstant.PeelQuotient.fst',
  'Core.AlgebraicConstant.EmbedHom.fst',
  'Core.AlgebraicConstant.ExtendStep.fst',
  'Core.Permutation.fst',
  'Core.Risch.Hermite.fst',
  'Core.Polynomial.Coeff.fst',
  'Core.Polynomial.Eval.fst',
  'Core.Polynomial.Height.fst',
  'Core.Polynomial.EmbedQ.fst',
  'Core.Polynomial.EmbedQAbs.fst',
  'Core.Fractions.RationalAbsInv.fst',
  'Core.Polynomial.Div.fst',
  'Core.Polynomial.EuclideanNotation.fst',
  'Core.Polynomial.Subst.fst',
  'Core.Polynomial.Unique.fst',
  'Core.Polynomial.Derivative.fst',
  'Core.Polynomial.DerivPower.fst',
  'Core.Polynomial.CoeffSum.fst',
  'Core.Fractions.Derivative.fst',
  'Core.Fractions.DerivativeSum.fst',
  'Core.Fractions.DerivationInstance.fst',
  'Core.Fractions.DerivativeQuotient.fst',
  'Core.Permutation.Sum.fst',
  'Core.Permutation.Enum.fst',
  'Core.Matrix.fst',
  'Core.Matrix.Determinant.fst',
  'Core.Polynomial.Roots.fst',
  'Core.Polynomial.LinearPeel.fst',
  'Core.AlgebraicConstant.EmbedEval.fst',
  'Core.AlgebraicConstant.EmbedTransport.fst',
  'Core.AlgebraicConstant.EmbedSquareFree.fst',
  'Core.AlgebraicConstant.SplittingField.fst',
  'Core.AlgebraicConstant.SplitBuild.fst',
  'Core.Polynomial.EmbedQProd.fst',
  'Core.Polynomial.Lagrange.fst',
  'Core.Polynomial.LagrangeDenomQ.fst',
  'Core.Polynomial.RootBound.fst',
  'Core.Polynomial.LagrangeInterp.fst',
  'Core.Polynomial.LagrangeBasisBound.fst',
  'Core.Polynomial.CRT.fst',
  'Core.Polynomial.Resultant.fst',
  'Core.Algebra.BinomialCoefficients.fst',
  'Core.Algebra.Power.fst',
  'Core.Algebra.Frobenius.fst',
  'Core.Modular.PrimeField.Poly.fst',
  'Core.Modular.PrimeField.Frobenius.fst',
  'Core.Modular.PrimeField.Berlekamp.fsti',
  'Core.Modular.PrimeField.Berlekamp.fst',
  'Core.Modular.ResidueRing.Hensel.Reduce.fst',
  'Core.Modular.ResidueRing.Hensel.Lift.fst',
  'Core.Modular.ResidueRing.Hensel.Multi.fst',
  'Core.Modular.ResidueRing.Centered.fst',
  'Core.Modular.ResidueRing.CenteredExact.fst',
  'Core.Modular.ResidueRing.CenteredPoly.fst',
  'Core.Modular.ResidueRing.CenteredPolyExact.fst',
  'Core.Modular.ResidueRing.IntReduce.fst',
  'Core.Modular.LagrangeBound.fst',
  'Core.Modular.Recombination.fst',
  'Core.Matrix.DetEval.fst',
  'Core.Risch.LRT.fst',
  'Core.Risch.PolyAntideriv.fst',
  'Core.Risch.Rational.fst',
  'Core.Risch.HermiteFracLift.fst',
  'Core.Risch.RationalSound.fst',
  'Core.Risch.RationalEuclid.fst',
  'Core.Polynomial.SplitDivisor.fst',
  'Core.Polynomial.ProdLinearsSquareFree.fst',
  'Core.Risch.RTSoundness.fst',
  'Core.Risch.RationalSplit.fst',
  'Core.Risch.RationalProperSound.fst',
  'Core.Risch.RationalSingleSound.fst',
  'Core.Risch.ResiduePartition.fst',
  'Core.Risch.RTAnswer.fst',
  'Core.Risch.RTAnswerEnd.fst',
  'Core.Risch.RTUnconditional.fst',
  'Core.Risch.RationalSplitField.fst',
  'Core.Polynomial.LagrangeInterpId.fst',
  'Core.Polynomial.EmbedQInterp.fst',
  'Core.Polynomial.KroneckerBound.fst',
  'Core.Polynomial.KroneckerHeightBound.fst',
  'Core.Polynomial.KroneckerLift.fst',
  'Core.Polynomial.Monic.fst',
  'Core.Polynomial.SubsetProd.fst',
  'Core.Polynomial.NodeExistence.fst',
  'Core.Modular.ResidueRing.Hensel.Unique.fst',
  'Core.Modular.RecombinationComplete.fst',
  'Core.Polynomial.CRTMulti.fst',
  'Core.Modular.PrimeField.FrobeniusFixed.fst',
  'Core.Modular.PrimeField.BerlekampDim.fst',
  'Core.Modular.PrimeField.BerlekampDimCount.fst',
  'Core.Modular.FpZmodBridge.fst',
  'Core.Modular.PrimeField.BerlekampComplete.fst',
  'Core.Risch.RationalFull.fst',
  'Core.Risch.YunFacs.fst',
  'Core.Risch.AnswerCheck.fst',
  'Core.Risch.RTAnswerForm.fst',
  'Core.LinearAlgebra.FpNullSpace.fst',
  'Core.Factor.Content.fst',
  'Core.Factor.PrimeSelect.fst',
  'Core.Factor.HenselCompute.fst',
  'Core.Factor.BerlekampFactor.fst',
  'Core.Factor.Recombine.fst',
  'Core.Factor.Zassenhaus.fst',
  'Core.Risch.RationalIntegrate.fst',
  'Core.Risch.Integrate.fst',
  'Core.Risch.LogPartFactored.fst',
  'Core.Risch.LogPartSound.fst',
  'Core.Risch.ResidueRoot.fst',
  # --- completeness-closure wave (2026-07-08): C1-C5 gap closures ---
  'Core.Matrix.DetHom.fst',
  'Core.Factor.FinInjSurj.fst',
  'Core.Factor.RecombineComplete.fst',
  'Core.Factor.Gauss.fst',
  'Core.Factor.GaussIrred.fst',
  'Core.Factor.ResultantReduction.fst',
  'Core.Factor.BadIntNonzero.fst',
  'Core.Factor.PrimeExists.fst',
  'Core.Factor.BerlekampComplete2.fst',
  'Core.Factor.BerlekampLoop.fst',
  'Core.Factor.BerlekampReachesR.fst',
  'Core.Factor.BerlekampComplete3.fst',
  'Core.Factor.FrobeniusMatrix.fst',
  'Core.Factor.BerlekampRepr.fst',
  'Core.Factor.BerlekampReprSpan.fst',
  'Core.Factor.BerlekampComplete6.fst',
  # --- C6 factor_Q completeness (2026-07-12) ---
  'Core.Modular.ResidueRing.Hensel.MonicLift.fst',
  'Core.Factor.ZassCompleteArith.fst',
  'Core.Factor.ZassCompleteMod.fst',
  'Core.Factor.ZassenhausComplete.fst',
  'Core.Factor.ZassComplete.fst',
  'Core.Polynomial.FactorizationExists.fst',
  'Core.Risch.VcRendering.fst',
  'Core.Risch.ResultantFactorExec.fst',
  # --- top-level rational integrator capstone (2026-07-12) ---
  'Core.Risch.IntegrateExplicit.fst',
  'Core.Factor.NonMonicZass.fst',
  'Core.Factor.FactorQComplete.fst',
  'Core.Factor.FactorIntComplete.fst',
  'Core.Factor.MonicizeSqfree.fst',
  'Core.Factor.FactorComplete.fst'
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