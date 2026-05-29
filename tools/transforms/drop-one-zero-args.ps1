<#
.SYNOPSIS
  Transform: Drop explicit #t #(cr.cr_r) on one/zero calls.
  
  Patterns like `one #t #(cr.cr_r)` or `zero #t #(cr.cr_r)` can often
  be simplified to just `one` or `zero` when there's enough type context.
  
  This is aggressive — some calls genuinely need the explicit args
  (e.g., inside lambdas where the type isn't constrained). The verify
  step will catch failures.
#>
param(
    [string]$Definition,
    [int]$Index,
    [string]$Name
)

$result = $Definition

# one #t #(cr.cr_r) -> one   (but NOT standalone one #t which may be needed)
$result = $result -replace '\bone\s+#t\s+#\(cr\.cr_r\)', 'one'

# zero #t #(cr.cr_r) -> zero
$result = $result -replace '\bzero\s+#t\s+#\(cr\.cr_r\)', 'zero'

# one #t -> one  (try this too — often inferrable)
$result = $result -replace '\bone\s+#t\b(?!\s+#)', 'one'

# zero #t -> zero
$result = $result -replace '\bzero\s+#t\b(?!\s+#)', 'zero'

if ($result -eq $Definition) {
    return $null
}
return $result
