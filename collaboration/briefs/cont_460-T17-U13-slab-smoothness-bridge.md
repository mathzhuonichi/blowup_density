# Lane 460 (continuation) — T17 U13: the slab bridge, second statement (global periodicity kept as a hypothesis, global smoothness dropped)

Same worktree/branch as before (`/data_8T/ping/blowup_density/.claude/worktrees/460-T17-U13-slab-smoothness-bridge`, branch `erenup/460-T17-U13-slab-smoothness-bridge`), same ground rules as `collaboration/briefs/460-T17-U13-slab-smoothness-bridge.md`
(read it again, plus your own `research/T17/REPORT_460.md`, `ATTEMPTS_U13.md`, `Section3/T17/SlabBridge.lean`). Your counterexample is accepted: `CorrectionAPI.reference_periodic : IsPeriodicOn univ v` is a *field*, so the first
`correctionStatementSlab` was false. Lead ruling (`research/T17/SPEC_ISSUES.md` §G5 addendum): T19 will feed the **zero extension** of the classical reference, `v_ext z := if z.1 ∈ Ico 0 (T+δ) then reference.velocity z else 0`,
which is `IsPeriodicOn univ` (periodic on `Ico 0 (T+δ)` by `velocity_periodic`, zero elsewhere) and `ContDiffOn ℝ ∞ (Ioo 0 (T+δ) ×ˢ univ)` (agrees with `reference.velocity` on that open set) but **not** globally smooth. So the
statement you must now prove keeps global periodicity and drops global smoothness:

```lean
def correctionStatementSlab' : Prop :=
  ∀ (ν : ℝ) (u : VelocityField) (p : PressureField) (f : VelocityField)
    (K : Set Space) (place : PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ),
    0 < ν → 0 < r → r < 1 / 2 → 0 < δ → IsPeriodicOn univ v →
    ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (place.T + δ) ×ˢ (univ : Set Space)) →
    (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ ball place.x₀ r, spatialDivergence v t x = 0) →
    (∀ t ∈ Ioo (0 : ℝ) 1, tsupport (fun x : Space ↦ u (t, x)) ⊆ K) →
    ball place.x₀ r ⊆ ball place.chartCenter place.chartRadius →
    ∃ D : CutoffData, LocalPotentialAPI v u place.Kstar place.x₀ r place.T δ D ∧
      Nonempty (CorrectionAPI ν place v r δ D)
theorem correctionStatementSlab'_holds : correctionStatementSlab'
```
Route (you already mapped the field dependencies): the only consumer of `ContDiff ℝ ∞ v` is the proof (`correctionAPI_of_smooth` → Paper1 profile lemmas), no *field* needs it. So: (1) `D := correctionData v place.x₀ place.T θ η O θR ε₀`
for the **original** `v`, with `hpot : LocalPotentialAPI v u … D` from the canonical T16 theorem `localPotentialAPI` (check its hypothesis list: it takes `IsPeriodicOn univ v` ✓ and a `ContDiffOn` on the cylinder ✓ — `hv.contDiffOn` in
`correctionStatementAmended_holds` was only a convenience; if it really needs global `ContDiff`, generalize as a new theorem). (2) For the remaining 44 fields: time cutoff `v' := fun z => χ z.1 • v z` with `χ` smooth, `χ = 1` on
`[T − m/2, T + m/2]`, `tsupport χ ⊆ Ioo (T − m) (T + m)`, `m := min place.T δ` (so `2ε² < m` for `ε ≤ ε₀` puts every window `[T − 2ε², T + 2ε²]` inside `χ = 1`); `ContDiff ℝ ∞ v'` (glue `Ioo 0 (T+δ) ×ˢ univ` where `v` is smooth
with the open complement of `tsupport χ ×ˢ univ` where `v' = 0`), `IsPeriodicOn univ v'`, divergence-free on the cylinder; run `correctionAPI_of_smooth ν place hv' r δ … hpot' (min_le_right _ _)` with `hpot' : LocalPotentialAPI v' u … D'`,
`D' := correctionData v' …` (same `θ η O θR ε₀`); then **transfer** `A' : CorrectionAPI ν place v' r δ D'` to `CorrectionAPI ν place v r δ D`: prove once that for `ε ∈ Ioc 0 ε₀` the objects coincide —
`D.correction ε = D'.correction ε` (`correctionData_correction` + `physicalCorrection v … ε = physicalCorrection v' … ε` because `physicalCorrection` reads `v` only at times `|t − T| ≤ 2ε²` through `η((t−T)/ε²)` and the potential of the
same slice), `correctionForce ν v D ε = correctionForce ν v' D' ε`, `rescaledCorrectionProfile v x₀ T ε D = rescaledCorrectionProfile v' x₀ T ε D'`, `rescaledForceProfile ν v … D = rescaledForceProfile ν v' … D'`, `rescaledReference v place ε =
rescaledReference v' place ε` on `fixedProfileCylinder D` — then each field of `A'` rewrites to the corresponding field for `(v, D)`; `reference_periodic` is the hypothesis; `potential` is `hpot`. Fields that quantify over all `ε` (not
just `Ioc 0 ε₀`) or read `v` off the window: list them explicitly and handle each (state the exact residual if one genuinely does not transfer). Keep `not_correctionStatementSlab` (it documents G5); add the new statement and theorem
to `SlabBridge.lean` (or a new `SlabBridge2.lean` if the module gets large). Probe `research/T17/probes/slab_from_classical.lean`: for `reference : ClassicalSolutionT ν a g (place.T + δ)`, define `v_ext` as above, prove
`IsPeriodicOn univ v_ext`, `ContDiffOn ℝ ∞ v_ext (Ioo 0 (place.T+δ) ×ˢ univ)`, the divergence clause from `reference.divergence`, and obtain `∃ D, LocalPotentialAPI v_ext … D ∧ Nonempty (CorrectionAPI ν place v_ext r δ D)` by `exact` —
this is the exact call T19 U0 will make. Update `research/T17/axioms_u13.lean`, `ATTEMPTS_U13.md`, `T17_SPLIT_U13.md`, and write `research/T17/REPORT_460b.md` (four parts). Same gates as before.
