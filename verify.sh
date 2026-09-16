#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

if grep -R -n -E '\b(sorry|admit|native_decide)\b|^[[:space:]]*axiom[[:space:]]' \
  --include='*.lean' .; then
  echo "Forbidden proof placeholder or project axiom found." >&2
  exit 1
fi

# Dependency revisions are pinned in lake-manifest.json.  Skip mathlib's
# optional binary-cache download so a GitHub Release outage does not prevent
# the source build below from running.
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build
lake env lean Audit.lean
sha256sum --check SHA256SUMS
