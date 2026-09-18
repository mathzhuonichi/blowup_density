# Lane 338-T11-U9e-existence-input-h3 — T11 U9e: prove the H³-ball existence input outright (lead amendment 2) and re-instantiate the continuation chain

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/338-T11-U9e-existence-input-h3` (git branch `erenup/338-T11-U9e-existence-input-h3`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalExistence,LocalExistenceProbe,ConvolutionBound,ConvolutionBoundReal,FractionalSmoothing,Persistence,DuhamelHalfStep,PhysicalRecovery,ClassicalAssembly,MildPressure,MildMomentum,MildClassical,Restart,CriterionBridge}.lean` (read `research/T11/LEAD_AMENDMENTS.md` amendments 1 and 2 and `EXISTENCE_ROUTE.md` (all U9 status sections) first: lane 313's `torusForcedPicard_exists` with explicit `TorusPicardConstants` (the Picard horizon in terms of the `H³` datum norm and the force bounds), lane 317's `torusTwoSpaceContract_nonempty'`, lane 330's `persistence_unconditional` and `exists_continuous_lerayForcePath`, lane 334's `mild_to_classical` / `exists_classical_of_picard`), `Section3/T10/{PeriodicData,ForcePaths}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/existence_input_h3_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U9e** under lead amendment 2 (`research/T11/LEAD_AMENDMENTS.md`): define
`def PeriodicQuantitativeLocalInputH3 : Prop` = `PeriodicQuantitativeLocalInput'` (lane 313, `LocalExistence.lean`) with `periodicSobolevENorm 3 a ≤ K` in place of `periodicSobolevENorm 1 a ≤ K`
(every other quantifier/hypothesis identical, incl. the order-wise force bounds `M`), and **prove it outright**: `theorem periodicQuantitativeLocalInputH3 : PeriodicQuantitativeLocalInputH3`.
Route: for `ν > 0`, `K ≠ ⊤`, `M` with `M m ≠ ⊤`: the two-space contract `C` (317), the datum `A` of `a` at order 3 (`CriterionBridge.exists_periodicDatum_smooth`) with `‖A‖ ≤ K.toReal`-type bound
from `periodicSobolevENorm 3 a ≤ K` (norm identification `CriterionBridge.periodicSobolevENorm_eq_*`), the continuous Leray force path `P` at order 3 from `g` (330's `exists_continuous_lerayForcePath`,
with its bound from `M 3`/`M 4` — check which orders the bound needs and derive it from `forceSobolevENormT 1 m g ≤ M m` via `ForcePaths.lean`), the Picard horizon `δ = δ(C, K, M)` from
`TorusPicardConstants` (313: read how the horizon is chosen — it must depend only on the datum-norm bound and the force bound, not on `a` itself; make that dependence explicit as a `def
picardHorizon ν K M`), the fixed point `u` (`torusForcedPicard_exists`), and finally `mild_to_classical`/`exists_classical_of_picard` (334) to produce `w : ClassicalSolutionT ν a g δ` with
`PeriodicLocalRegularity`. Then the re-instantiations: `restartH3` (lane 321's `restart` proof with the `H³` ball — copy the theorem with the changed ball; it is the same argument), and
`extendsBeyondH3`/`lifespanInfiniteOfLocallyFiniteH3`/`exists_maximal_unconditional` by feeding `periodicQuantitativeLocalInputH3` into 332/337/323's theorems where the ball choice allows
(where a theorem quantifies over the `H¹` ball internally, state the `H³` variant and prove it by the same proof). **No named input**: this lane discharges the last one on the existence line;
if a step is out of reach, honest partial with the exact obstacle. Also write `research/T11/H1_GAP.md`: the exact `H¹`-ball statements that remain unproved (`PeriodicQuantitativeLocalInput'`,
the V1 `restart`), why (Fujita–Kato subcritical theory absent), and the consumer check list for U17 (which downstream fields use which ball). (L, Opus.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/ExistenceInputH3.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_existence_input_h3.lean`.
2. Records `research/T11/ATTEMPTS_EXISTENCE_INPUT_H3.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_338.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.ExistenceInputH3` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[338-T11] ExistenceInputH3`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
