<#
.SYNOPSIS
  Transform: remove redundant `let ID : commutative_ring (...) = TC.solve in`
  binders (in requires/ensures/body) and the explicit `#(...) #ID`, `#(ID.…)`,
  `#ID` threadings that go with them. The polynomial/element commutative_ring is
  resolved by TC, so this plumbing is slop. Verify+rollback keeps only the
  definitions where TC genuinely resolves the instance.
#>
param([string]$Definition, [int]$Index, [string]$Name)

$d = $Definition

# collect binder names: let ID : commutative_ring (...) = TC.solve in
$ids = @()
foreach ($m in [regex]::Matches($d, 'let\s+(\w+)\s*:\s*commutative_ring\s*\([^=]*=\s*(?:TC\.solve|FStar\.Tactics\.Typeclasses\.solve)\s*in')) {
    $ids += $m.Groups[1].Value
}
if ($ids.Count -eq 0) { return $null }

# drop the binder occurrences (keeps surrounding `=`/`(` / newline -> still valid)
$d = [regex]::Replace($d, 'let\s+\w+\s*:\s*commutative_ring\s*\([^=]*=\s*(?:TC\.solve|FStar\.Tactics\.Typeclasses\.solve)\s*in', '')

foreach ($id in ($ids | Select-Object -Unique)) {
    $e = [regex]::Escape($id)
    # `#(SomeType) #ID ` (explicit type + instance) — most common
    $d = [regex]::Replace($d, '#\([^()]*\)\s+#' + $e + '(?!\w)', '')
    # `#(ID.cr_r.r_add.acg_eq)` etc. (equatable projection on the binder)
    $d = [regex]::Replace($d, '#\(' + $e + '\.[^()]*\)', '')
    # bare `#ID`
    $d = [regex]::Replace($d, '#' + $e + '(?!\w)', '')
}

if ($d -eq $Definition) { return $null }
return $d
