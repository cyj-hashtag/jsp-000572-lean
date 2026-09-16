$ErrorActionPreference = "Stop"
Set-Location $PSScriptRoot

$forbidden = Get-ChildItem -Recurse -Filter *.lean | Select-String `
  -Pattern '\b(sorry|admit|native_decide)\b', '^[\s]*axiom[\s]'
if ($forbidden) {
  $forbidden | ForEach-Object { Write-Error $_.ToString() }
  throw "Forbidden proof placeholder or project axiom found."
}

$previousNoCache = $env:MATHLIB_NO_CACHE_ON_UPDATE
try {
  # Dependency revisions are pinned in lake-manifest.json. Skip mathlib's
  # optional binary-cache download; lake build still checks the Lean sources.
  $env:MATHLIB_NO_CACHE_ON_UPDATE = "1"
  lake update
  if ($LASTEXITCODE -ne 0) { throw "lake update failed" }
} finally {
  $env:MATHLIB_NO_CACHE_ON_UPDATE = $previousNoCache
}
lake build
if ($LASTEXITCODE -ne 0) { throw "lake build failed" }
lake env lean Audit.lean
if ($LASTEXITCODE -ne 0) { throw "axiom audit failed" }

Get-Content SHA256SUMS | ForEach-Object {
  if ($_ -notmatch '^([0-9a-f]{64})  (.+)$') {
    throw "Invalid SHA256SUMS line: $_"
  }
  $actual = (Get-FileHash -Algorithm SHA256 -LiteralPath $Matches[2]).Hash.ToLowerInvariant()
  if ($actual -ne $Matches[1]) {
    throw "SHA-256 mismatch: $($Matches[2])"
  }
}
