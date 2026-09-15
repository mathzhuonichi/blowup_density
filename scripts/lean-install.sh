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
# Guard: lake must be run from verification/. If someone runs it inside formalization/ by
# mistake, Lake treats that directory as its own workspace and would clone and compile Mathlib
# from source (2.8 GB, hours). Pointing its packages directory at the shared clone makes that
# mistake harmless instead.
if [ ! -e "$WT/formalization/.lake/packages" ] && [ -d "$ROOT/verification/.lake/packages" ]; then
  mkdir -p "$WT/formalization/.lake" && ln -s "$ROOT/verification/.lake/packages" "$WT/formalization/.lake/packages"
  echo "== linked formalization/.lake/packages -> $ROOT/verification/.lake/packages"
fi
# Seed this worktree's build outputs from the integration worktree (or the main checkout) so a new
# lane pays seconds, not an hour, before its first lake build; lake re-checks traces and rebuilds
# only what differs.
SEED="${LEAN_SEED_DIR:-$ROOT/.claude/worktrees/000-integration}"
[ -d "$SEED/formalization/.lake/build" ] || SEED="$ROOT"
for sub in formalization vendor/NavierStokesAndEuler verification; do
  if [ "$WT" != "$SEED" ] && [ ! -d "$WT/$sub/.lake/build" ] && [ -d "$SEED/$sub/.lake/build" ]; then
    mkdir -p "$WT/$sub/.lake" && cp -r "$SEED/$sub/.lake/build" "$WT/$sub/.lake/build"
    echo "== seeded $sub/.lake/build from $SEED"
  fi
done
echo "== lake exe cache get"
lake exe cache get
echo "== lake test"
lake test
echo "== OK"
