# Lane 309-T11-U2-criterion-bridge — T11 U2 — datum existence, finiteness, and the H² criterion bridge to `FiniteH2Energy`

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/309-T11-U2-criterion-bridge` (git branch `erenup/309-T11-U2-criterion-bridge`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/criterion_bridge_closes.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U2** of `T11_SPLIT.md` §1 (base includes lane 308's `Section3/T11/FlowConversion.lean` — `toFlow`): (a) every smooth periodic `z` has an order-`s` datum at every real `s`, hence
`periodicSobolevENorm s z ≠ ⊤` (componentwise `smoothPeriodicWeightedFourierLp`, `Paper1/PeriodicSmoothSobolev.lean:45`, + `realPeriodicSubmodule` membership + Haar integrability; or via
`Section3/T10/FourierCalculus.lean` decay); (b) `periodicSobolevENorm s z = ENNReal.ofReal (periodicVectorSobolevNorm s …)` via `T01.torus_data`'s `datum_unique` and
`norm_smoothPeriodicWeightedFourierLp :53`; (c) measurability of `t ↦ periodicSobolevENorm 2 (u (t,·))` from `ClassicalSolutionT.sobolev`'s continuous datum path; (d) **both directions** of
`squaredHTwoIntegralT S w.velocity ≠ ⊤ ↔ FiniteH2Energy (toFlow w)` (`PeriodicLocalLifespan.lean:60`, land via `PeriodicFiniteH2Bridge.lean:25`). No named input expected.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/CriterionBridge.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_criterion_bridge.lean`.
2. Records `research/T11/ATTEMPTS_CRITERION_BRIDGE.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_309.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.CriterionBridge` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[309-T11] CriterionBridge`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
