# Lane 315-T11-U5-uniqueness — T11 U5 — uniqueness package (`velocity_unique`, `pressure_unique`, `horizon_le_lifespan`)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/315-T11-U5-uniqueness` (git branch `erenup/315-T11-U5-uniqueness`, based on `origin/erenup/integration-section3`: canonical modules
`formalization/NSFormalization/Section3/T10/{PeriodicData,PhysicalBridge,DatumBasics,Parseval,Leray,FourierCalculus}.lean` (FourierCalculus only if lane 305 has landed — check `ls`),
`Section3/T11/LocalTheory.lean`, `Section3/T12/*.lean`, the registered contract `verification/Contracts/V1/TorusData.lean` (`T01.torus_data`), and the proof targets
`research/T11/probes/api_on_canonical.lean`). Read `CLAUDE.md` (hard rules; "结构体例外"), **`research/T11/T11_SPLIT.md` (binding: §0 ground rules, your unit's entry in §1, §3 risks, §4 conversions)**,
`research/T11/RECONCILIATION.md` §0–§3, `research/T11/IMPLEMENTATION_CANDIDATES.md`, and the top 40 lines of `logs/LESSONS.md` (**name every instance explicitly**; no anonymous `local instance`).

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed.
- Lean: `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`.
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. New files only; no edits to existing modules.
- **Satisfiability / peeling rule** (`T11_SPLIT.md` §0): if your unit must assume something not yet proved, name exactly ONE input hypothesis with its exact statement as a `def … : Prop`
  (the split names it where applicable), prove everything else from it, and record it; never weaken a target statement. Target statements are the fields of
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/uniqueness_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U5** of `T11_SPLIT.md` §1 (base includes lane 308's `Section3/T11/FlowConversion.lean` — `toFlow` — and lane 309's `CriterionBridge.lean`): the three fields verbatim from
`research/T11/probes/api_on_canonical.lean`: `velocity_unique` and `pressure_unique` (pointwise on `Ico 0 (min T₁ T₂)`): `toFlow` both solutions; `w.pressure_gauge` + `pressureMeanT = cubeIntegral`
(from `Paper1/TorusCube.lean`'s `integral_torusLift`) gives `IsNormalized (toFlow w)` (`Paper1/PeriodicLocalLifespan.lean:44`); then `normalized_flows_agree` (`:229`) verbatim, plus
`flow_velocity_agree_on_common_interval` (`:175`) for the velocity. `horizon_le_lifespan` is `le_iSup_of_le T (le_iSup_of_le ⟨w⟩ le_rfl)` on `maximalLifespanT` (`Section3/T10/PeriodicData.lean`) — no
conversion. No named input expected. (M, sol.)

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/Uniqueness.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_uniqueness.lean`.
2. Records `research/T11/ATTEMPTS_UNIQUENESS.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_315.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.Uniqueness` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[315-T11] Uniqueness`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
