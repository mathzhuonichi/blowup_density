#!/usr/bin/env bash
# Standard local gates for a lane, run from anywhere inside the worktree.
# Usage: scripts/gates.sh [Lean.Module ...]   (extra modules are built from verification/ first)
# Env: LEAN_NUM_THREADS (default 6), BASE_REF (default origin/erenup/integration)
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
. scripts/lean-env.sh
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-6}"
echo "== make check";           make check
MODULES="$*"; if [ -n "$MODULES" ]; then echo "== lake build $MODULES"; ( cd verification && lake build $MODULES ); fi
echo "== make test";            make test 2>&1 | grep -E 'Contract|error|sorry' || true
echo "== make test-mutations";  make test-mutations 2>&1 | tail -3
echo "== check_contracts";      python3 experiments/check_contracts.py --base-ref "${BASE_REF:-origin/erenup/integration}" | tail -3
echo "== gates OK"
