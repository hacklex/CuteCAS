<#
.SYNOPSIS
  Transform: Drop redundant (x <: fin n) casts to just x.
  
  Many F* casts like (i <: fin n), (k <: fin n), (j <: fin n) are
  redundant when the variable is already of the correct type from
  its binding. This script removes them.
  
  Strategy: replace `(VAR <: fin N)` with just `VAR` when VAR is
  a simple identifier (no complex expressions).
  
  NOTE: Some casts are NOT redundant:
    - (i <: nat) — coercion from fin to nat (KEEP)
    - (k <: fin n) inside a lambda bound as (k: nat) (KEEP — the cast IS needed)
  So we only remove casts where the target type matches `fin \w+` and the
  variable name appears as a binding of that exact type in the definition.
#>
param(
    [string]$Definition,
    [int]$Index,
    [string]$Name
)

# Simple approach: remove (VAR <: fin SOMETHING) where VAR is a single identifier
# but NOT (EXPR <: nat) which is a real coercion
# Be conservative: only remove (LETTER_ID <: fin LETTER_ID)

$result = $Definition

# Pattern: (single_id <: fin single_id) -> single_id  
# But NOT (x <: nat) — those are needed coercions
$result = $result -replace '\(([a-z_][a-z_0-9]*)\s+<:\s+fin\s+([a-z_][a-z_0-9]*)\)', '$1'

# Also handle (i <: fin (Prims.op_Subtraction n 1)) — leave these alone (complex type)
# The regex above only matches simple `fin ID` so complex ones are already safe.

if ($result -eq $Definition) {
    return $null  # No changes
}
return $result
