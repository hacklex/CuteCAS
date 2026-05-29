<#
.SYNOPSIS
  Transform: Simplify fun (x: nat) -> to fun x -> where possible.
  
  Many lambda arguments like `fun (j: nat) ->` can be simplified to
  `fun j ->` when the type is inferrable from context.
  
  Conservative: only handles `fun (ID: nat) ->` and `fun (ID: t) ->`
  patterns where t is a simple type name.
#>
param(
    [string]$Definition,
    [int]$Index,
    [string]$Name
)

$result = $Definition

# fun (x: nat) -> ... => fun x -> ...
$result = $result -replace 'fun\s+\(([a-z_][a-z_0-9]*):\s*nat\)\s*->', 'fun $1 ->'

# fun (x: t) -> ... => fun x -> ... (where t is a single lowercase id)  
$result = $result -replace 'fun\s+\(([a-z_][a-z_0-9]*):\s*([a-z_][a-z_0-9]*)\)\s*->', 'fun $1 ->'

if ($result -eq $Definition) {
    return $null
}
return $result
