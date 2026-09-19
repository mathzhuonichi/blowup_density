import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.ForceVolume

/-!
# Probe: the two volume/duration fields close on the concrete correction

The two `example`s first pin the *shape* of the canonical `CorrectionAPI`
fields `force_spatial_volume` / `force_time_length`
(`Section3/T17/Correction.lean:182,188`, `research/T17/Spec.lean:861,866`):
projecting a hypothetical record at the concrete `correctionData` produces
exactly those statements, with the record's own real constant
`A.spatialVolumeConst`.

The following theorems then restate the same statements with `D` replaced by
`correctionData` and `A.spatialVolumeConst` replaced by the explicit
`spatialVolumeConst θR = (4/3)π θR³` of `Section3/T17/ForceVolume.lean`, and
close each of them directly by `exact`.  `fields_at_placement` is the same at
the canonical `place.x₀` / `place.T` spelling, together with the
nonnegativity datum `spatialVolumeConst_nonneg`.

The last theorem instantiates both fields on T16's cutoffs at a nonzero
constant, divergence-free, periodic reference, so neither is vacuous; it is
lane 425's non-vacuity witness.
-/

noncomputable section

namespace NSFormalization.Section3.T17.Probe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn periodicTorusMeasure)
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology ENNReal BigOperators

/-! ## Field conformance: the two statements are literally the record fields -/

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      periodicTorusMeasure (torusSpatialSupport
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (A.spatialVolumeConst * ε ^ 3) :=
  A.force_spatial_volume

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      volume (torusTemporalSupport
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (4 * ε ^ 2) :=
  A.force_time_length

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    0 ≤ A.spatialVolumeConst :=
  A.spatialVolumeConst_nonneg

/-! ## The Spec fields, with the concrete `D := correctionData ...` -/

theorem field_force_spatial_volume (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2) (hθR : 0 ≤ θR)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      periodicTorusMeasure (torusSpatialSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3) := by
  exact force_spatial_volume ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc
    hθsupp hηsupp hr2 hθR hεtime hεspace

theorem field_force_time_length (ν : ℝ) {v : SpaceTimeField}
    (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T δ r : ℝ)
    (hvper : IsPeriodicOn univ v)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR)
    (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hr2 : r < 1 / 2)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      volume (torusTemporalSupport
          (correctionForce ν v (correctionData v x₀ T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (4 * ε ^ 2) := by
  exact force_time_length ν hv x₀ T δ r hvper O θR ε₀ hθ hη hθc hηc
    hθsupp hηsupp hr2 hεtime hεspace

/-- The U8 data and the two U8 theorems, instantiated at `place.x₀` /
`place.T`: this is the `exact` probe asked for by the lane. -/
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
    (hr2 : r < 1 / 2) (hθR : 0 ≤ θR)
    (hεtime : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < min place.T δ)
    (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    (0 ≤ spatialVolumeConst θR) ∧
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      periodicTorusMeasure (torusSpatialSupport
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3)) ∧
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      volume (torusTemporalSupport
          (correctionForce ν v (correctionData v place.x₀ place.T θ η O θR ε₀) ε)) ≤
        ENNReal.ofReal (4 * ε ^ 2)) :=
  ⟨spatialVolumeConst_nonneg hθR,
   force_spatial_volume ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc
      hθsupp hηsupp hr2 hθR hεtime hεspace,
   force_time_length ν hv place.x₀ place.T δ r hvper O θR ε₀ hθ hη hθc hηc
      hθsupp hηsupp hr2 hεtime hεspace⟩

/-! ## Non-vacuity on a nonzero constant reference and the T16 cutoffs -/

theorem nonvacuous_force_volume :
    ∃ (v : SpaceTimeField) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ),
      v ≠ 0 ∧ 0 < ε₀ ∧ 0 < θR ∧
      (∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0) ∧
      0 ≤ spatialVolumeConst θR ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
        periodicTorusMeasure (torusSpatialSupport
            (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε)) ≤
          ENNReal.ofReal (spatialVolumeConst θR * ε ^ 3)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v 0 1 θ η O θR ε₀).ε₀,
        volume (torusTemporalSupport
            (correctionForce 1 v (correctionData v 0 1 θ η O θR ε₀) ε)) ≤
          ENNReal.ofReal (4 * ε ^ 2)) := by
  obtain ⟨θR, θ, O, hθR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₀, hε₀pos, hεtime, hεspace⟩ :=
    exists_threshold hθR (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
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
  refine ⟨v, θ, η, O, θR, ε₀, hvne, hε₀pos, hθR, hvdiv, spatialVolumeConst_nonneg hθR.le, ?_, ?_⟩
  · exact force_spatial_volume 1 hv 0 1 1 (1 / 4) hvper O θR ε₀ hθsm hηsm hθcs hηcs
      hθsupp hηsupp (by norm_num) hθR.le hεtime hεspace
  · exact force_time_length 1 hv 0 1 1 (1 / 4) hvper O θR ε₀ hθsm hηsm hθcs hηcs
      hθsupp hηsupp (by norm_num) hεtime hεspace

end NSFormalization.Section3.T17.Probe
