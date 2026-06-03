<#
.SYNOPSIS
  Transform: replace explicit `poly_mul_commutativity` with the general
  `mul_commutativity_cr` (available once the polynomial commutative_ring instance
  is in scope). Same for the other poly-specific ring laws that have a general
  counterpart. Verify+rollback guards correctness.
#>
param([string]$Definition, [int]$Index, [string]$Name)

$d = $Definition
$d = $d -replace '\bpoly_mul_commutativity\b', 'mul_commutativity_cr'

if ($d -eq $Definition) { return $null }
return $d
