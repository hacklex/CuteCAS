<#
.SYNOPSIS
  Transform: collapse explicit equational-law plumbing once BOTH
  `elim_equatable_laws X ()` (reflexivity + symmetry) and `trans_for_calc X ()`
  (transitivity) are in scope — together they expose all three laws as foralls,
  so explicit `symmetry`/`transitivity`/`reflexivity` (+ `poly_eq_*`) calls become
  redundant.

  Steps (per definition):
    1. If exactly one of {elim_equatable_laws, trans_for_calc} is present, add the
       missing companion (same type arg, same H. prefix, same indentation).
    2. Collapse any aux/`let` body that is PURELY such calls to `()`.
    3. Drop remaining standalone `;`-terminated such calls.

  The framework's verify+rollback keeps the definition only if the result still
  verifies, so over-collapsing is automatically reverted.
#>
param([string]$Definition, [int]$Index, [string]$Name)

$d = $Definition

# --- detect helper presence + the (X) type argument + optional H. prefix ----
$elimRe  = '(H\.)?elim_equatable_laws\s+(\([^)]*\)|\S+)\s*\(\)'
$transRe = '(H\.)?trans_for_calc\s+(\([^)]*\)|\S+)\s*\(\)'
$prefix = ''; $arg = $null
if ($d -match $elimRe)      { $prefix = $Matches[1]; $arg = $Matches[2] }
elseif ($d -match $transRe) { $prefix = $Matches[1]; $arg = $Matches[2] }
else { return $null }                       # no equational-law helper here

$hasElim  = [bool]($d -match $elimRe)
$hasTrans = [bool]($d -match $transRe)

# --- 1. add the missing companion right after the present one ----------------
if ($hasElim -and -not $hasTrans) {
    $d = [regex]::Replace($d, '([ \t]*)((H\.)?elim_equatable_laws\s+' + [regex]::Escape($arg) + '\s*\(\)\s*;)',
        { param($m) $m.Groups[1].Value + $m.Groups[2].Value + "`n" + $m.Groups[1].Value + $prefix + "trans_for_calc $arg ();" }, 1)
    $hasTrans = $true
} elseif ($hasTrans -and -not $hasElim) {
    $d = [regex]::Replace($d, '([ \t]*)((H\.)?trans_for_calc\s+' + [regex]::Escape($arg) + '\s*\(\)\s*;)',
        { param($m) $m.Groups[1].Value + $m.Groups[2].Value + "`n" + $m.Groups[1].Value + $prefix + "elim_equatable_laws $arg ();" }, 1)
    $hasElim = $true
}

$eqcall = '(?:H\.)?(?:symmetry|transitivity|reflexivity|poly_eq_symmetry|poly_eq_transitivity|poly_eq_reflexivity)\b'

# --- 2. collapse a body that is purely eq-law calls to () --------------------
#   `= eqcall; eqcall; … eqcall  in`  ->  `= ()  in`
$d = [regex]::Replace($d,
    '(?ms)(=[ \t]*\r?\n?)(?:[ \t]*' + $eqcall + '[^\r\n]*(?:;[ \t]*)?\r?\n?)+([ \t]*\bin\b)',
    ('$1()' + "`n" + '$2'))
#   trailing body (def-final, no `in`): `= eqcall; … eqcall<EOF>` -> `= ()`
$d = [regex]::Replace($d,
    '(?ms)(=[ \t]*\r?\n?)(?:[ \t]*' + $eqcall + '[^\r\n]*(?:;[ \t]*)?\r?\n?)+$',
    ('$1()' + "`n"))

# --- 3. drop remaining standalone `;`-terminated eq-law statement lines ------
$lines = $d -split "`n"
$kept = foreach ($ln in $lines) {
    if ($ln -match '^\s*' + $eqcall + '[^;]*;\s*(\(\*.*)?$') { continue }
    $ln
}
$d = ($kept -join "`n")

if ($d -eq $Definition) { return $null }
return $d
