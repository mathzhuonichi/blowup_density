#!/usr/bin/env bash
# Re-create the U05 toolchain probe workspace.
#
# The probe is a throwaway Lake package that compiles a *copy* of
# vendor/HeliCorgi/Formal against our pinned toolchain (leanprover/lean4:v4.34.0-rc2)
# and our pinned Mathlib (85e3a25e006c35636f0e53b0e9296caca2685bc0).
#
# It never downloads Mathlib: .lake/packages is a symlink to the already
# materialised shared package directory of the main verification package.
#
# Usage:  bash research/U05/probe/make_probe.sh   (from anywhere)
set -euo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"          # .../research/U05/probe
WT="$(cd "$HERE/../../.." && pwd)"                            # worktree root
SHARED_PACKAGES="${SHARED_PACKAGES:-/data_8T/ping/blowup_density/verification/.lake/packages}"

if [[ ! -d "$SHARED_PACKAGES/mathlib" ]]; then
  echo "error: shared package dir not found: $SHARED_PACKAGES" >&2
  exit 1
fi

# 1. Fresh copy of the vendored HeliCorgi sources (never edit vendor/ in place).
rm -rf "$HERE/Formal"
cp -a "$WT/vendor/HeliCorgi/Formal" "$HERE/Formal"

# 2. Borrow the already-resolved manifest so Lake does not try to re-resolve.
cp "$WT/vendor/NavierStokesAndEuler/lake-manifest.json" "$HERE/lake-manifest.json"

# 3. Point .lake/packages at the shared, already-built package tree.
mkdir -p "$HERE/.lake"
rm -rf "$HERE/.lake/packages"
ln -s "$SHARED_PACKAGES" "$HERE/.lake/packages"

echo "probe ready at $HERE"
echo "  toolchain : $(cat "$HERE/lean-toolchain")"
echo "  mathlib   : $(git -C "$SHARED_PACKAGES/mathlib" rev-parse HEAD)"
echo "  modules   : $(ls "$HERE/Formal"/*.lean | wc -l) .lean files"
