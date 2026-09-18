# Lane 323-T11-U15-maximal — T11 U15 — `exists_maximal` + `maximal_unique` (+ `maximalLifespanT = PeriodicLifespan.lifespan`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/323-T11-U15-maximal` (git branch `erenup/323-T11-U15-maximal`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/{LocalTheory,FlowConversion,CriterionBridge,LocalExistenceProbe,LocalExistence,ConvolutionBound,GalileanClasses,PhysicalRecovery,Rescaling,Uniqueness,MeanIdentity}.lean` (T11 wave 1–2 results; `LocalExistence.lean` defines the named existence input `PeriodicQuantitativeLocalInput'` — `research/T11/LEAD_AMENDMENTS.md` amendment 1), `Section3/T10/{FourierCalculus,ForcePaths}.lean` (ForcePaths only if lane 312 has landed — check `ls`), `Section3/T12/{MeanZeroCalculus,SpectralGap}.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/maximal_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U15** of `T11_SPLIT.md` §1 and §4 (last row): `exists_maximal` and `maximal_unique` of `PeriodicLocalTheoryAPI` verbatim from `research/T11/probes/api_on_canonical.lean`. Route: `0 < maximalLifespanT ν a f`
from U11's `solution`/`horizon` (lane 321 — if it has not landed, take exactly ONE named input: the existence of some `ClassicalSolutionT ν a f T` with `T > 0` for `a ∈ initialClassT`, `f ∈ forceClassT`, `ν > 0`,
stated as a `def … : Prop`); gluing by `Paper1/PeriodicLocalLifespan.lean:411` `exists_maximal_periodic_solution_of_lifespan_pos` (unconditional) after `toFlow` (lane 308), then `ofFlow` back at each horizon
(the three extra fields — `sobolev`, `pressure_gradient`, `pressure_gauge` — come from the horizon-wise `ClassicalSolutionT`s via uniqueness, lane 315's `Uniqueness.lean`); `maximal_unique` at presingular
times: from `IsMaximalPeriodicSolution` (`Section3/T11/LocalTheory.lean`) pick `S` with `t < S` and `ofReal S < maximalLifespanT` (`ENNReal` supremum density: `lt_iSup_iff`), then `velocity_unique`/`pressure_unique`.
Also prove `maximalLifespanT ν a f = PeriodicLifespan.lifespan ν a f` (the §4 last row; both are suprema over horizons of solutions — the conversions give both inequalities). (M, sol.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/Maximal.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_maximal.lean`.
2. Records `research/T11/ATTEMPTS_MAXIMAL.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_323.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Maximal` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[323-T11] Maximal`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
