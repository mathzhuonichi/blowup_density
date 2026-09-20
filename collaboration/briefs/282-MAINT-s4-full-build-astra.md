# Lane 282-MAINT-s4-full-build-astra — independent full build of the Section 4 deliverable (frozen branch `erenup/integration`, PR #259)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) **verification** worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/282-MAINT-s4-full-build-astra` (git branch `erenup/282-MAINT-s4-full-build-astra`,
based on `origin/erenup/integration`, the frozen Section 4 branch that is PR #259 → `main`). Read `CLAUDE.md` (Lean environment section:
`. scripts/lean-env.sh`; `lake` only from `verification/`; `LEAN_NUM_THREADS=6`) first.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- **Change nothing** except the one new report file below: no edits to `.lean` files, contracts, tests, ledgers, scripts.
- Do not read `logs/SECTION4_FULL_BUILD_20260917.md` (an earlier verifier's report) until your own build and gates have finished; this run must be independent. Compare afterwards.

## Task
Verify from scratch that the Section 4 deliverable on this commit compiles completely and passes the gates.
1. `git rev-parse HEAD`; record toolchain (`lean --version`, `lake --version`, Mathlib rev from `verification/lake-manifest.json`).
2. Enumerate every module under `formalization/NSFormalization/Section4/` (`find … -name '*.lean'`, not only `git ls-files`) — report the count.
3. **Genuine re-elaboration**: delete the build products of those modules only (`formalization/.lake/build/lib/lean/NSFormalization/Section4/` and `formalization/.lake/build/ir/NSFormalization/Section4/` if present; keep Mathlib/vendor caches), then one `cd verification && LEAN_NUM_THREADS=6 lake build <all Section4 module names>` (pass all module names on one command line, generated from the enumeration). Record wall time, exit code, error count (must be 0), warning count with a classification (which files, whether replayed from `vendor/HeliCorgi` / `Source/Paper3` or from Section 4 sources).
4. Gates from the worktree root: `make check`, `make test`, `make test-mutations`, and `python3 experiments/check_contracts.py --base-ref main` (report `registered_contracts` and `base_compatibility_checked`).
5. Axiom audit: for every registered contract in `verification/contracts.json` confirm the Tests module's `checkAxioms` output is `propext, Classical.choice, Quot.sound` only (run `make test` output or `lake env lean` on each `verification/Tests/*.lean`); report the count of audited declarations.
6. Forbidden tokens: `grep -rnE "^\s*(axiom|sorry|admit)\b|native_decide" formalization/NSFormalization/Section4 verification/Contracts verification/Bindings verification/Tests` — list any hit (prose mentions inside docstrings are fine; say so). Also list every `set_option maxHeartbeats N` with `N > 400000` in Section 4 sources.
7. Only after all of the above: read `logs/SECTION4_FULL_BUILD_20260917.md` and state agreements/disagreements.

## Deliverable
`logs/SECTION4_FULL_BUILD_20260917_ASTRA.md` (English or Chinese; sections: environment / full build / gates / axiom audit / forbidden tokens & heartbeats / comparison with the earlier report / exact commands with their outputs' key lines). Commit it on your branch as `[282-MAINT] Section 4 full build report (astra)`. Logs go to `tmp/` (gitignored).

## Report
End with four parts: what was verified / what the tree contains (module & contract counts) / any gap or anomaly (with exact error text) / commands and results.
