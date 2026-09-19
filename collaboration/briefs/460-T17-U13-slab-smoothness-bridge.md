# Lane 460-T17-U13-slab-smoothness-bridge — T17 U13: `correctionStatementSlab` (the registered T17 correction block under the hypotheses a classical reference actually has)

You are a Lean 4 (v4.34.0-rc2 + Mathlib) proof worker on the repository checked out at your working directory
`/data_8T/ping/blowup_density/.claude/worktrees/460-T17-U13-slab-smoothness-bridge` (git branch `erenup/460-T17-U13-slab-smoothness-bridge`, = `origin/erenup/integration-section3`).
Read `CLAUDE.md`, **`research/T17/SPEC_ISSUES.md` §G5** (the finding this lane closes; also G1, G3, G4), `research/T17/RECONCILIATION.md` §3/§4, `formalization/NSFormalization/Section3/T17/Assembly.lean` (all of it:
`correctionStatementAmended`, `correctionAPI_of_smooth` and `correctionStatementAmended_holds`, and every place `hv : ContDiff ℝ ∞ v` / `hper : IsPeriodicOn univ v` is consumed), `Section3/T17/Correction.lean`
(`CorrectionAPI`, 45 fields; note which fields mention `v`: `potential`, `reference_periodic`, the two rescaled profiles, `correctionForce ν v D ε`), `Section3/T17/Transport.lean` (`correctionData`, `physicalCorrection`,
`latticeLift`), `Section3/T16/LocalPotential.lean` (`LocalPotentialAPI`, `localPotentialData`, the canonical `localPotentialAPI` theorem and its hypotheses `hper`/`hv.contDiffOn`), the Paper1 profile lemmas it relies on
(`Paper1/CorrectionProfile.lean`: `profile_smooth`, `profile_uniform_global_derivative_bound`, …), `verification/Contracts/V1/TorusLocalTheory.lean:130-200` (`ClassicalSolutionT`: `velocity_smooth : ContDiffOn ℝ ∞ velocity (Ico 0 T ×ˢ univ)`,
`velocity_periodic : IsPeriodicOn (Ico 0 T) velocity`), the top 40 lines of `logs/LESSONS.md`.

## Ground rules (non-negotiable)
- Work ONLY inside this worktree; never `git push`, merge or rebase; committing on your branch is allowed. `. scripts/lean-env.sh`; `lake` only from `verification/` with `LEAN_NUM_THREADS=6`. Build the closure you need first
  (`lake build NSFormalization.Section3.T17.Assembly`).
- No `sorry`/`admit`/`axiom`/`native_decide`; `set_option maxHeartbeats N in` only per declaration, `N ≤ 400000`, commented. **No edits to existing modules, contracts, bindings or tests** — new files only (generalized T16/T17
  theorems are *new* declarations in new files; existing signatures stay untouched because the bindings depend on them).
- **No named inputs, no placeholders, no goal repackaging.** An honest partial with the exact residual statement and error text beats a stub; a stub is rejected outright.
- Every declaration prints exactly `[propext, Classical.choice, Quot.sound]`. `grep -rn` before claiming "not in the tree"; `sed -n` before citing a line. Record every failed approach with its exact error text in the ATTEMPTS file.

## Why (the gap)
T18's `InsertionData` (lane 455, `Section3/T18/Assembly.lean`) types its correction as `CorrectionAPI ν place reference.velocity r δ D` with `reference : ClassicalSolutionT ν a g (place.T + δ)`. T19 must build it from
`RegularThroughT`, but the registered `correctionStatementAmended` needs **global** `ContDiff ℝ ∞ v` and **global** `IsPeriodicOn univ v`, while a classical solution only gives smoothness/periodicity on `Ico 0 (T+δ)`
(its velocity is arbitrary for `t < 0`; no smooth extension across `t = 0` exists in the tree). So the correction must be produced under the slab hypotheses. Everything the correction really uses lives in the window
`t ∈ [T − 2ε², T + 2ε²] ⊂ (0, T+δ)` (`eps_time : 2ε² < min T δ`), `x ∈ ball x₀ (ε·θR) ⊂ ball x₀ r` — except the T16 `potential` field, whose `potential_formula` is `∀ t x` and whose `potential_curl` is over the whole cylinder
`Ioo 0 (T+δ) × ball x₀ r`.

## Goal
New module `formalization/NSFormalization/Section3/T17/SlabBridge.lean` (namespace `NSFormalization.Section3.T17`) with
```lean
def correctionStatementSlab : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ →
    IsPeriodicOn (Ico (0 : ℝ) (place.T + δ)) v →
    ContDiffOn ℝ ∞ v (Ico (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r, spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)
theorem correctionStatementSlab_holds : correctionStatementSlab
```
(same shape as `correctionStatementAmended`, only the two global hypotheses replaced by the `ClassicalSolutionT` ones; `IsPeriodicOn` is the registered predicate — check its definition, it may already be set-relative in the right way).
Route, choose the cheapest that closes and record the choice: **(i)** define the time cutoff `v' := fun z => χ z.1 • v z` with `χ` smooth, `χ = 1` on `[T − m/2, T + m/2]`, `tsupport χ ⊆ Ioo (T − m) (T + m)`, `m := min T δ`
(reuse `exists_timeCutoff`-style constructions from T16/T17); show `ContDiff ℝ ∞ v'` (`v'` is `χ·v` on the open slab `Ioo 0 (T+δ) ×ˢ univ` where `v` is smooth, and `0` on an open complement — glue with `contDiff_iff_contDiffAt`),
`IsPeriodicOn univ v'`, divergence-free on the cylinder; run the existing `correctionStatementAmended_holds` (or `correctionAPI_of_smooth` + `localPotentialAPI`) on `v'`; then transfer every window-local field back to `v`
with the same cutoff parameters `θ η O θR ε₀` (window agreement: `rescaledCorrectionProfile`, `rescaledForceProfile`, `correctionForce`, `physicalCorrection` only read `v` on the window, where `v' = v`); for the `potential`
field and `D` itself (`correctionData v …` vs `correctionData v' …`) decide whether `D := correctionData v …` (potential of the *original* `v`) can be used — this needs the T16 canonical proof under the slab hypotheses:
state and prove a **new** theorem `localPotentialAPI_slab` (new file `Section3/T16/SlabPotential.lean` or inside `SlabBridge.lean`) whose hypotheses are `IsPeriodicOn (Ico 0 (T+δ)) v` and `ContDiffOn ℝ ∞ v (Ioo 0 (T+δ) ×ˢ ball x₀ r)`,
by reusing the existing lemmas (check exactly where `hper : IsPeriodicOn univ v` is consumed; if only at cylinder times, the generalization is mechanical). **(ii)** if (i)'s potential transfer is blocked, re-prove the
`hv`-consuming fields of `correctionAPI_of_smooth` directly under the slab hypotheses by applying the Paper1 profile lemmas to `v'` and rewriting the profile objects along window agreement.
Deliverables: the module(s); probe `research/T17/probes/slab_from_classical.lean` that, for an arbitrary `reference : ClassicalSolutionT ν a g (place.T + δ)` with the divergence/support/ball hypotheses, obtains
`∃ D, LocalPotentialAPI reference.velocity … D ∧ Nonempty (CorrectionAPI ν place reference.velocity r δ D)` by `exact correctionStatementSlab_holds … reference.velocity_periodic reference.velocity_smooth …`
(this is exactly what T19's threading unit will call); `research/T17/axioms_u13.lean`; `research/T17/ATTEMPTS_U13.md`; a U13 status line in `research/T17/T17_SPLIT.md` (or the T17 split file that exists — grep). If one field
genuinely cannot be obtained under the slab hypotheses, deliver everything else as an honest partial (a structure-valued theorem for the fields that close is NOT acceptable as a substitute for the statement; instead state the
exact residual field, its statement, and the missing lemma) — that residual decides whether a T16/T17 V2 is needed.

## Gates
`cd verification && LEAN_NUM_THREADS=6 lake build NSFormalization.Section3.T17.SlabBridge` (0 errors), `lake env lean` on each new module (0 output), the probe, the axioms file, `make check`.

## Report
Commit on your branch; end with four parts (theorem with exact statement / files / gaps with error text / commands and results). Also write it to `research/T17/REPORT_460.md`.
