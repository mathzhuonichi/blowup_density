# Lane 311-T11-U9a-existence-probe — T11 U9a — the periodic local-existence route probe (R1 HeliCorgi endpoint layer vs R2 A01 cylinder route), the `T³` two-space contract

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/311-T11-U9a-existence-probe` (git branch `erenup/311-T11-U9a-existence-probe`, based on `origin/erenup/integration-section3`: canonical modules
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
  `research/T11/probes/api_on_canonical.lean` (or the bridge lemmas the split states) — copy them verbatim; a probe `research/T11/probes/existence_probe.lean` must show each target closes.
- Before claiming a lemma is "not in the tree", `grep -rn` `formalization/NSFormalization/Paper1/Periodic*.lean`, `Section3/`, `Section4/{A01,A02,A04,D01}`, `vendor/HeliCorgi/Formal/`.
  Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`; include a non-vacuity `example`.

## Goal
Unit **U9a** of `T11_SPLIT.md` §1 (U9, first sub-lane; critical path). Fix the named input exactly as the split states it:
```
def PeriodicQuantitativeLocalInput : Prop := ∀ ν : ℝ, 0 < ν → ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧ ∀ a : SpatialField, a ∈ initialClassT → periodicSobolevENorm 1 a ≤ K →
  ∀ g : SpaceTimeField, ContDiff ℝ ∞ g → IsPeriodicOn univ g → (∀ m : ℕ, forceSobolevENormT 1 (m : ℝ) g ≤ K) → ∃ w : ClassicalSolutionT ν a g δ, PeriodicLocalRegularity ν a g δ w
```
and **decide the route with evidence**: (R1) instantiate HeliCorgi's abstract layer on the torus carrier — read `vendor/HeliCorgi/Formal/UniformRestartContinuation.lean` (`FlowMapUniformRestartPackage :29`,
`:59`), `EndpointSafeTwoSpaceDuhamel.lean`, and the periodic Picard/Duhamel modules already in the tree (`Paper1/PeriodicPicardContraction.lean`, `PeriodicPicardDuhamelLipschitz.lean`,
`PeriodicMildWitnessAdapter.lean`, `PeriodicShearLocal.lean`, `PeriodicLocalLifespan.lean`'s `ClassicalPeriodicLocalTheory` fields `local_flow`/`finite_h2_extension`): write the exact `T³`
two-space contract (carrier, Duhamel operator, contraction constants) as Lean `structure`s/`def`s and prove whatever is provable now (e.g. the coefficient-side heat semigroup bounds, the
bilinear estimate in the form the package needs, or the reduction "package ⇒ `PeriodicQuantitativeLocalInput`"); (R2) otherwise copy A01's cylinder route (`Section4/A01/Horizon.lean`,
`AprioriInvariance.lean`) to the coefficient level and prove the first rung. Deliver: the contract statements, at least one genuinely proved reduction or rung (not just definitions), and a
written decision `research/T11/EXISTENCE_ROUTE.md` (which route, why, the sub-lane list U9b… with exact statements and sizes). Astra: this is the long pole; do not stop at definitions.

## Deliverables
1. New module `formalization/NSFormalization/Section3/T11/LocalExistenceProbe.lean` (namespace `NSFormalization.Section3.T11`); the probe; conformance `research/T11/axioms_existence_probe.lean`.
2. Records `research/T11/ATTEMPTS_EXISTENCE_PROBE.md` (paths tried, exact error text, any residual named input with its exact statement); report `research/T11/REPORT_311.md`; update your unit's row in
   `research/T11/T11_SPLIT.md` §1 with a one-line status (append only).

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T11.LocalExistenceProbe` (0 errors), `lake env lean` on the module, the probe and the axioms file, `make check` from the worktree root.

## Report
Commit on your branch (`[311-T11] LocalExistenceProbe`); end with four parts (theorems with exact statements / files / gaps with error text / commands and results).
