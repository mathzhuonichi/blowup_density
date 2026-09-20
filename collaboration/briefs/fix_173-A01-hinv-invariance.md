# Rework for lane 173-A01-hinv-invariance — export the full seven-clause bound-invariant continuation (review REJECT)

Worktree: `/data_8T/ping/blowup_density/.claude/worktrees/173-A01-hinv-invariance` (branch
`erenup/173-A01-hinv-invariance`, your commit `75e3b1c`). Work only here; never `git push`, merge or rebase;
committing on this branch is allowed. Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with
`LEAN_NUM_THREADS=6`. Rules as before (no `sorry`/`admit`/`axiom`/`native_decide`; standard three axioms;
this lane's own files only).

Read `research/A01/REVIEW_173-A01-hinv-invariance.md` (verdict REJECT) and its probe
`research/A01/probes/rev173_consumer_mismatch.lean` (the reproducing error). Finding: your
`forced_global_mild_of_boundInv` returns **four** clauses, whereas the consumer it must replace,
`Continuation.forced_global_of_bound_unconditional` (and `Horizon.localTheory_on_prescribed_horizon`,
`Section4/A01/Horizon.lean:137-157`), returns **seven** (the mild solution `u`, the ordinary-`L²` path `U`,
`‖u‖ ≤ R`, `u 0 = ordinarySobolev …`, `U 0 = a.toLp`, the descent `ordinaryLift (U t) = value 1 (u t)`,
divergence-freeness, the forced Duhamel equation and angle invariance — take the exact list from the
consumer's statement). Apply the review's fixes exactly:
1. In `formalization/NSFormalization/Section4/A01/AprioriInvariance.lean`, export
   `forced_global_of_boundInv` whose conclusion is **token-identical** to
   `forced_global_of_bound_unconditional`'s (only the hypothesis `HasAprioriBound` replaced by
   `HasAprioriBoundInv`), and likewise make `localTheory_on_prescribed_horizon_of_boundInv`'s conclusion
   token-identical to `localTheory_on_prescribed_horizon`'s. Keep the current four-clause theorem only as a
   clearly named helper (e.g. `forced_global_mild_core_of_boundInv`) with a docstring saying it is the core.
2. Update `research/A01/REPORT_173.md`, `ATTEMPTS_HINV.md`, the lane-173 note in `A3_SPLIT.md`, and
   `research/A01/axioms_hinv.lean` (`#print axioms` for every declaration; the non-vacuity example should
   exercise the full seven-clause export).
Rerun `lake build NSFormalization.Section4.A01.AprioriInvariance` (silent), `lake env lean` on the module
(0 output), the axioms file, `make check`, and — to prove the match — a probe
`research/A01/probes/fix173_consumer_match.lean` that `exact`s the new theorem against a verbatim
restatement of `forced_global_of_bound_unconditional`'s conclusion under `HasAprioriBoundInv`.
Commit; end with a short report (final statements, gate outputs).
