#!/usr/bin/env bash
set -euo pipefail

proof_url=https://github.com/cyj-hashtag/jsp-000572-lean.git
proof_sha=527bfcac522f9edf120301f63a0c7672d691f651
checker_sha=aeaca0f19e8ff3ab8e0c98a52985cba7dcfb2234

echo "started_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
uname -a
export DEBIAN_FRONTEND=noninteractive
apt-get update
apt-get install -y --no-install-recommends ca-certificates curl git zstd
rm -rf /var/lib/apt/lists/*
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  | sh -s -- -y --default-toolchain leanprover/lean4:v4.20.0
export PATH=/root/.elan/bin:$PATH
lake --version
lean --version

git clone --no-checkout -- "$proof_url" /work/proof
git -C /work/proof checkout --detach "$proof_sha"
test "$(git -C /work/proof rev-parse HEAD)" = "$proof_sha"
test -z "$(git -C /work/proof status --porcelain)"

cd /work/proof
export MATHLIB_NO_CACHE_ON_UPDATE=1
lake update
test "$(git -C .lake/packages/mathlib rev-parse HEAD)" = c211948581bde9846a99e32d97a03f0d5307c31e
unset MATHLIB_NO_CACHE_ON_UPDATE
lake exe cache get
test ! -e .lake/build/lib/lean/Problem572.olean
test ! -e .lake/build/lib/lean/Problem572

lake build
lake build +Problem572.Main
lake env lean Problem572/Main.lean
lake env lean Audit.lean

git clone --no-checkout -- https://github.com/leanprover/lean4checker.git /work/lean4checker
git -C /work/lean4checker checkout --detach "$checker_sha"
test "$(git -C /work/lean4checker rev-parse HEAD)" = "$checker_sha"
(cd /work/lean4checker && lake build lean4checker)
lake env /work/lean4checker/.lake/build/bin/lean4checker Problem572.Main

test "$(git rev-parse HEAD)" = "$proof_sha"
test -z "$(git status --porcelain)"
echo "completed_utc=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
