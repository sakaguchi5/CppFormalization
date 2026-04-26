param(
  [string]$RepoRoot = "."
)

$ErrorActionPreference = "Stop"

function Write-Utf8NoBom {
  param(
    [Parameter(Mandatory = $true)][string]$Path,
    [Parameter(Mandatory = $true)][string]$Content
  )
  $encoding = New-Object System.Text.UTF8Encoding($false)
  [System.IO.File]::WriteAllText($Path, $Content, $encoding)
}

$transitions = Join-Path $RepoRoot "CppFormalization/Cpp2/Closure/Transitions"
$oldPath = Join-Path $transitions "Major/DeclareRefDecomposition.lean"
$newDir = Join-Path $transitions "DeclareRef"
$newPath = Join-Path $newDir "Preservation.lean"
$allPath = Join-Path $newDir "All.lean"

if (-not (Test-Path $oldPath)) {
  throw "Missing source file: $oldPath"
}

if (-not (Test-Path $newDir)) {
  New-Item -ItemType Directory -Force -Path $newDir | Out-Null
}

$content = Get-Content -Raw -Encoding UTF8 $oldPath
$content = $content -replace '# Closure\.Transitions\.Major\.DeclareRefDecomposition', '# Closure.Transitions.DeclareRef.Preservation'
Write-Utf8NoBom -Path $newPath -Content $content

$allContent = @'
import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.Preservation
'@
Write-Utf8NoBom -Path $allPath -Content ($allContent + "`n")

$stubContent = @'
import CppFormalization.Cpp2.Closure.Transitions.DeclareRef.Preservation

/-!
# Closure.Transitions.Major.DeclareRefDecomposition

Deprecated compatibility stub.

The canonical DeclareRef transition preservation surface now lives in
`Closure.Transitions.DeclareRef.Preservation`.
-/
'@
Write-Utf8NoBom -Path $oldPath -Content $stubContent

Write-Host "Moved DeclareRef preservation surface to: $newPath"
Write-Host "Replaced old Major.DeclareRefDecomposition with compatibility stub."
