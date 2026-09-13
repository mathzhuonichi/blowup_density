#!/usr/bin/env bash
# Self-contained Lean setup: elan + pinned toolchain + Mathlib cache + acceptance tests.
# Idempotent. cd into the checkout or worktree you want set up, then:  bash /data_8T/ping/blowup_density/scripts/lean-install.sh
# Everything lands in <main checkout>/.elan and verification/.lake (both gitignored). ~11 GB.
set -euo pipefail
# ROOT = main checkout (shared toolchain + package clones); WT = the worktree you run this from (cwd).
ROOT="$(dirname "$(git rev-parse --path-format=absolute --git-common-dir)")"
WT="$(git rev-parse --show-toplevel)"
export ELAN_HOME="$ROOT/.elan"
export PATH="$ELAN_HOME/bin:$PATH"
mkdir -p "$ELAN_HOME"
if ! command -v elan >/dev/null 2>&1; then
  echo "== install elan into $ELAN_HOME"
  curl -sSfL https://elan.lean-lang.org/elan-init.sh -o "$ELAN_HOME/elan-init.sh"
  sh "$ELAN_HOME/elan-init.sh" -y --no-modify-path --default-toolchain none
fi
elan --version
cd "$WT/verification"
elan toolchain install "$(cat lean-toolchain)" || true
lean --version
# A worktree shares the main checkout's dependency clones instead of re-downloading 8 GB.
if [ "$WT" != "$ROOT" ] && [ ! -e .lake/packages ] && [ -d "$ROOT/verification/.lake/packages" ]; then
  mkdir -p .lake && ln -s "$ROOT/verification/.lake/packages" .lake/packages
  echo "== linked .lake/packages -> $ROOT/verification/.lake/packages"
fi
echo "== lake exe cache get"
lake exe cache get
echo "== lake test"
lake test
echo "== OK"
