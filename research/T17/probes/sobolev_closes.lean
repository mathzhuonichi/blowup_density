import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.Sobolev
import NSFormalization.Section3.T17.Correction

/-!
# Probe: the U11 `eq:HHs` fields close on the concrete correction

The first three theorems restate the canonical `CorrectionAPI` fields
`sobolevConst_pos` / `forceSobolev_memLp` / `force_sobolev_bound`
(`Section3/T17/Correction.lean:262-282`, `research/T17/Spec.lean:944-960`) with
`D` replaced by the concrete `correctionData` and the record's `sobolevConst`
replaced by the module's explicit `sobolevConst ν hv x₀ T hθ hη hθc hηc`; each
is closed directly by `exact`.

The three `example`s project the same three fields out of a hypothetical
`CorrectionAPI`, giving two-sided type conformance against the canonical record.
The final theorem instantiates the two quantitative fields on T16's cutoffs at a
nonzero constant, divergence-free, periodic reference centred in the cube, so
neither is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T17.SobolevProbe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn forceSobolevENormT)
open NSFormalization.Section3.T15 (MemForceSobolevT)
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology BigOperators

/-! ## The Spec fields, with the concrete `D := correctionData ...` -/

theorem field_sobolevConst_pos (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < sobolevConst ν hv x₀ T hθ hη hθc hηc s := by
  exact sobolevConst_pos ν hv x₀ T hθ hη hθc hηc

theorem field_forceSobolev_memLp (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        MemForceSobolevT 1 s
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) := by
  exact forceSobolev_memLp ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc
    hθsupp hηsupp hr2 hε₀ hεtime hεspace

theorem field_force_sobolev_bound (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
        forceSobolevENormT 1 s
            (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε) ≤
          ENNReal.ofReal
            (sobolevConst ν hv x₀ T hθ hη hθc hηc s *
              (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) := by
  exact force_sobolev_bound ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc
    hθsupp hηsupp hr2 hε₀ hεtime hεspace

/-! ## Two-sided conformance: the record's own projections have these types -/

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < A.sobolevConst s :=
  A.sobolevConst_pos

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
        MemForceSobolevT 1 s
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) :=
  A.forceSobolev_memLp

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
        forceSobolevENormT 1 s
            (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) ≤
          ENNReal.ofReal
            (A.sobolevConst s * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s))) :=
  A.force_sobolev_bound

/-! ## The two quantitative fields at `place.x₀` / `place.T` -/

theorem fields_at_placement (ν : ℝ) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v) (δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hε₀ : ε₀ ≤ 1)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        0 < sobolevConst ν hv place.x₀ place.T hθ hη hθc hηc s) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
        MemForceSobolevT 1 s
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
        forceSobolevENormT 1 s
            (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε) ≤
          ENNReal.ofReal
            (sobolevConst ν hv place.x₀ place.T hθ hη hθc hηc s *
              (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))) :=
  ⟨sobolevConst_pos ν hv place.x₀ place.T hθ hη hθc hηc,
    forceSobolev_memLp ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc
      hθsupp hηsupp hr2 hε₀ hεtime hεspace,
    force_sobolev_bound ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc
      hθsupp hηsupp hr2 hε₀ hεtime hεspace⟩

/-! ## Non-vacuity on a nonzero constant reference at the cube centre -/

theorem nonvacuous_sobolev :
    ∃ (v : SpaceTimeField) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space)
        (θR ε₀ : ℝ) (C : ℝ → ℝ),
      v ≠ 0 ∧ 0 < ε₀ ∧
      (∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 < C s) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
          MemForceSobolevT 1 s
            (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε)) ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
          forceSobolevENormT 1 s
              (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε) ≤
            ENNReal.ofReal
              (C s * (ε ^ ((3 : ℝ) / 2) + ε ^ ((3 : ℝ) / 2 - s)))) := by
  obtain ⟨θR, θ, O, hθR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₀, hε₀pos, hεtime, hεspace⟩ :=
    exists_threshold hθR (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let ε₁ := min ε₀ 1
  have hε₁pos : 0 < ε₁ := lt_min hε₀pos one_pos
  have hε₁le : ε₁ ≤ 1 := min_le_right _ _
  have htime₁ : ∀ ε ∈ Ioc (0 : ℝ) ε₁, 2 * ε ^ 2 < min (1 : ℝ) 1 := by
    intro ε hε
    exact hεtime ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have hspace₁ : ∀ ε ∈ Ioc (0 : ℝ) ε₁, ε * θR < (1 / 4 : ℝ) := by
    intro ε hε
    exact hεspace ε ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  let v : SpaceTimeField := fun _ => coordinateVector 0
  have hv : ContDiff ℝ ∞ v := contDiff_const
  have hvper : IsPeriodicOn univ v := fun _ _ _ _ => rfl
  have hvdiv : ∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0 := by
    intro t x
    simp [spatialDivergence, spatialDerivative, v]
  have hvne : v ≠ 0 := by
    intro h
    have h0 := congrFun h ((0 : ℝ), (0 : Space))
    simp only [v, Pi.zero_apply] at h0
    have hc : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [h0]; rfl
    simp [coordinateVector] at hc
  refine ⟨v, θ, η, O, θR, ε₁, sobolevConst 1 hv 0 1 hθsm hηsm hθcs hηcs,
    hvne, hε₁pos, hvdiv, sobolevConst_pos 1 hv 0 1 hθsm hηsm hθcs hηcs, ?_, ?_⟩
  · exact forceSobolev_memLp 1 hv 0 1 1 (1 / 4) hvper O θR ε₁
      hθsm hηsm hθcs hηcs hθsupp hηsupp (by norm_num) hε₁le htime₁ hspace₁
  · exact force_sobolev_bound 1 hv 0 1 1 (1 / 4) hvper O θR ε₁
      hθsm hηsm hθcs hηcs hθsupp hηsupp (by norm_num) hε₁le htime₁ hspace₁

end NSFormalization.Section3.T17.SobolevProbe

#print axioms NSFormalization.Section3.T17.SobolevProbe.field_sobolevConst_pos
#print axioms NSFormalization.Section3.T17.SobolevProbe.field_forceSobolev_memLp
#print axioms NSFormalization.Section3.T17.SobolevProbe.field_force_sobolev_bound
#print axioms NSFormalization.Section3.T17.SobolevProbe.fields_at_placement
#print axioms NSFormalization.Section3.T17.SobolevProbe.nonvacuous_sobolev
