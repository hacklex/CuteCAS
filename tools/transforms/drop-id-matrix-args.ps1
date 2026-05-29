<#
.SYNOPSIS
  Transform: Simplify id_matrix explicit arguments.
  
  Replace `id_matrix #t #_ #n` with `id_matrix #t` — the wildcard
  and dimension arguments auto-resolve from context.
  Also: `id_matrix_off #t #_ #n` -> `id_matrix_off #t`
#>
param(
    [string]$Definition,
    [int]$Index,
    [string]$Name
)

$result = $Definition

# id_matrix #t #_ #n -> id_matrix #t
$result = $result -replace 'id_matrix\s+#t\s+#_\s+#n\b', 'id_matrix #t'

# id_matrix_off #t #_ #n -> id_matrix_off #t  
$result = $result -replace 'id_matrix_off\s+#t\s+#_\s+#n\b', 'id_matrix_off #t'

if ($result -eq $Definition) {
    return $null
}
return $result
