# Lane 332-T11-U13-restart-beyond — T11 U13 — `restartBeyond`: patch the `SolvesBelowT` pair with the restart solution into one `ClassicalSolutionT ν a f (S+δ)`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/332-T11-U13-restart-beyond` (git branch `erenup/332-T11-U13-restart-beyond`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,GalileanClasses,Rescaling,Uniqueness,MeanIdentity,Restart,Maximal,Persistence,ClassicalAssembly,DuhamelHalfStep}.lean` (all T11 units landed so far: U1–U5, U7, U10, U11, U15; `GalileanClasses.lean` has the translation isometry and class transports, `Rescaling.lean` the viscosity algebra, `MeanIdentity.lean` translation/mean lemmas, `Restart.lean` the `restart` theorem from the existence input), `Section3/T10/{FourierCalculus,ForcePaths}.lean`, `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/restart_beyond_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U13** of `T11_SPLIT.md` §1: the `restartBeyond` field of `PeriodicContinuationAPI` verbatim from `research/T11/probes/api_on_canonical.lean` (read its exact statement: `∃ δ > 0` **before**
the datum, uniform over the `H¹` ball `K`; from `SolvesBelowT ν a f S u p` with the `H¹` trajectory bound, a `ClassicalSolutionT ν a f (S + δ)` agreeing with `(u, p)` on `[0, S)`). Route: take `δ`
from lane 321's `restart` (`Section3/T11/Restart.lean`, hypothesis `PeriodicQuantitativeLocalInput'` — the **single allowed named input**, exactly as there) at the `H¹` bound `K` for the fixed
`f` and `S`; pick `t₀ ∈ [S − δ/2, S)` (so `t₀ + δ > S`), restart from the slice `u(t₀,·)` (in `initialClassT` with `periodicSobolevENorm 1 ≤ K` by the trajectory bound; the shifted force
`timeShiftT t₀ f`), and glue: on `[0, t₀]` keep `(u, p)`, on `[t₀, t₀ + δ)` use the restarted solution shifted back in time; agreement on the overlap by uniqueness (`Uniqueness.lean`:
`velocity_unique`/`pressure_unique` applied to the two solutions of the shifted problem on their common interval — the `SolvesBelowT` pair restricted to `[t₀, S)` is a `ClassicalSolutionT`
for the shifted data by `SolvesBelowT`'s definition; check `LocalTheory.lean`), then assemble the glued `ClassicalSolutionT ν a f (S + δ)` field by field (piecewise definition; smoothness across
`t₀` from the overlap agreement on an open interval; the datum path glued continuously; **exact** normalized-pressure agreement on `[0,S)`: "needs a lemma" ⑩ — both pressures are gauge-normalized
and their gradients agree, so they agree by `pressure_unique`; overlap bookkeeping as `Paper1/PeriodicLocalLifespan.lean:564` `extension_agrees_on_common_interval`). Export the gluing constructor
(`glueClassicalSolutionT`) for U14/U16. (M–L, sol.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/RestartBeyond.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_restart_beyond.lean`.
2. Records `research/T11/ATTEMPTS_RESTART_BEYOND.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_332.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.RestartBeyond` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[332-T11] RestartBeyond`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
