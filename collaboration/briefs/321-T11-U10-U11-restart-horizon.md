# Lane 321-T11-U10-U11-restart-horizon — T11 U10 + U11 — `restart` from the named existence input; `horizon` / `solution` / `regularity`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/321-T11-U10-U11-restart-horizon` (git branch `erenup/321-T11-U10-U11-restart-horizon`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/restart_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Units **U10** and **U11** of `T11_SPLIT.md` §1 (read them and `research/T11/LEAD_AMENDMENTS.md` amendment 1). **Single allowed named input**: `PeriodicQuantitativeLocalInput'` exactly as defined
in `Section3/T11/LocalExistence.lean` (it is being discharged by U9d/U9e in parallel; you take it as the hypothesis of your theorems, never restate or weaken it). Prove, verbatim from
`research/T11/probes/api_on_canonical.lean`: (U10) the `restart` field of `PeriodicContinuationAPI` — for fixed `f ∈ forceClassT`, `S ≥ 0`, finite `K`, there is `δ > 0` such that for every `t₀ ∈ Icc 0 S`
and every `a' ∈ initialClassT` with `periodicSobolevENorm 1 a' ≤ K` there is a `ClassicalSolutionT ν a' (timeShiftT t₀ f) δ` with `PeriodicLocalRegularity`: instantiate the input with the
order-wise bounds `M m := forceSobolevENormT 1 m f` (prove `forceSobolevENormT 1 m (timeShiftT t₀ f) ≤ forceSobolevENormT 1 m f` for `t₀ ≥ 0` — translation of the time integral; and `M m ≠ ⊤` from lane 312's
`ForcePaths` if landed, else from `CriterionBridge`/`FourierCalculus` slicewise + compact time support — say which), `timeShiftT t₀ f` smooth and periodic; (U11) `horizon`, `solution`, `regularity` of
`PeriodicLocalTheoryAPI`: `restart` at `S = 0`, `t₀ = 0`, `K := periodicSobolevENorm 1 a` (finite by `CriterionBridge.periodicSobolevENorm_ne_top_smooth`), `timeShiftT 0 f = f`; `horizon` extracted by
`Classical.choice`, defaulting to `1` off the class (as the split says); package as `def periodicLocalTheoryAPI_of_input (H : PeriodicQuantitativeLocalInput') : PeriodicLocalTheoryAPI`-style partial
assembly for the three fields (the other five come from U5/U15/U16 later). (M, sol.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/Restart.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_restart.lean`.
2. Records `research/T11/ATTEMPTS_RESTART.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_321.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Restart` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[321-T11] Restart`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
