import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.Energy
import NSFormalization.Section3.T17.Correction

/-!
# Probe: the four U9 fields close on the concrete correction

The first three theorems restate the canonical `CorrectionAPI` fields
`correction_slice_memLp` / `correction_gradient_memLp` /
`correction_energy_bound` (`Section3/T17/Correction.lean:223-241`,
`research/T17/Spec.lean:900-920`) with `D` replaced by the concrete
`correctionData` and `place.x₀`, `place.T` replaced by the bare `x₀`, `T`; each
is closed directly by `exact`.  The record's `energyConst` / `energyConst_nonneg`
are supplied by the module's `energyConst` and `energyConst_nonneg`.

`hcube_of_placement` shows that the one geometric premise beyond lane 425's
cutoff block is *not* a new assumption: it is the canonical `PlacementData`
field `chartBall_in_cube` composed with the canonical `CorrectionAPI` field
`ball_in_chart`.

The last theorem instantiates all four conclusions on T16's cutoffs at a
nonzero constant, divergence-free reference placed at the centre of the
fundamental cube, so none of them is vacuous.
-/

noncomputable section

namespace NSFormalization.Section3.T17.Probe

open Set MeasureTheory Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13 (fundamentalCube fundamentalCubeInterior
  interior_fundamentalCube)
open NSFormalization.Section3.T16
open NSFormalization.Section4.I02 (spatialGradient)
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff ENNReal Topology BigOperators

/-! ## The Spec fields, with the concrete `D := correctionData ...` -/

theorem field_correction_slice_memLp {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift
          (fun x : Space => (correctionData v x₀ T θ η O θR ε₀).correction ε (t, x))) 2
        periodicTorusMeasure := by
  exact correction_slice_memLp hv x₀ T O θR ε₀ hθ hη hθc hηc hθsupp hηsupp

theorem field_correction_gradient_memLp {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) (θR ε₀ : ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x : Space =>
          spatialGradient ((correctionData v x₀ T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure := by
  exact correction_gradient_memLp hv x₀ T O θR ε₀ hθ hη hθc hηc hθsupp hηsupp

theorem field_correction_energy_bound {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR r ε₀ : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hcube : closure (ball x₀ r) ⊆ interior fundamentalCube)
    (hε₀ : ε₀ ≤ 1) (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v x₀ T θ η O θR ε₀).ε₀,
      energyENormT T ((correctionData v x₀ T θ η O θR ε₀).correction ε) ≤
        ENNReal.ofReal (energyConst hv x₀ T hθ hη hθc hηc * ε ^ ((3 : ℝ) / 2)) := by
  exact correction_energy_bound hv x₀ T O hθ hη hθc hηc hθsupp hηsupp hcube hε₀ hεspace

/-! ## Field conformance: the statements are literally the record fields -/

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x : Space =>
          (correctionData v place.x₀ place.T θ η O θR ε₀).correction ε (t, x))) 2
        periodicTorusMeasure :=
  A.correction_slice_memLp

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x : Space =>
          spatialGradient
            ((correctionData v place.x₀ place.T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure :=
  A.correction_gradient_memLp

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
    (A : CorrectionAPI ν place v r δ
      (correctionData v place.x₀ place.T θ η O θR ε₀)) :
    ∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      energyENormT place.T
          ((correctionData v place.x₀ place.T θ η O θR ε₀).correction ε) ≤
        ENNReal.ofReal (A.energyConst * ε ^ ((3 : ℝ) / 2)) :=
  A.correction_energy_bound

example (ν : ℝ) {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (A : CorrectionAPI ν place v r δ D) : 0 ≤ A.energyConst :=
  A.energyConst_nonneg

/-! ## The geometric premise is a consequence of the canonical records -/

/-- The one placement premise of `correction_energy_bound` beyond lane 425's
cutoff block is exactly `PlacementData.chartBall_in_cube` composed with
`CorrectionAPI.ball_in_chart`; it is not an extra assumption. -/
theorem hcube_of_placement (ν : ℝ) {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    (v : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (A : CorrectionAPI ν place v r δ D) :
    closure (ball place.x₀ r) ⊆ interior fundamentalCube :=
  (closure_mono A.ball_in_chart).trans place.chartBall_in_cube

/-! ## All four conclusions at `place.x₀` / `place.T` -/

theorem fields_at_placement {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData u p f K)
    {v : SpaceTimeField} (hv : ContDiff ℝ ∞ v)
    {θ : Space → ℝ} {η : ℝ → ℝ} (O : Set Space) {θR r ε₀ : ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθsupp : tsupport θ ⊆ ball (0 : Space) θR) (hηsupp : tsupport η ⊆ Ioo (-2 : ℝ) 2)
    (hcube : closure (ball place.x₀ r) ⊆ interior fundamentalCube)
    (hε₀ : ε₀ ≤ 1) (hεspace : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ε * θR < r) :
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x : Space =>
          (correctionData v place.x₀ place.T θ η O θR ε₀).correction ε (t, x))) 2
        periodicTorusMeasure) ∧
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀, ∀ t : ℝ,
      MemLp (torusLift (fun x : Space =>
          spatialGradient
            ((correctionData v place.x₀ place.T θ η O θR ε₀).correction ε) t x)) 2
        periodicTorusMeasure) ∧
    0 ≤ energyConst hv place.x₀ place.T hθ hη hθc hηc ∧
    (∀ ε ∈ Ioc (0 : ℝ) (correctionData v place.x₀ place.T θ η O θR ε₀).ε₀,
      energyENormT place.T
          ((correctionData v place.x₀ place.T θ η O θR ε₀).correction ε) ≤
        ENNReal.ofReal
          (energyConst hv place.x₀ place.T hθ hη hθc hηc * ε ^ ((3 : ℝ) / 2))) :=
  ⟨correction_slice_memLp hv place.x₀ place.T O θR ε₀ hθ hη hθc hηc hθsupp hηsupp,
   correction_gradient_memLp hv place.x₀ place.T O θR ε₀ hθ hη hθc hηc hθsupp hηsupp,
   energyConst_nonneg hv place.x₀ place.T hθ hη hθc hηc,
   correction_energy_bound hv place.x₀ place.T O hθ hη hθc hηc hθsupp hηsupp hcube
     hε₀ hεspace⟩

/-! ## Non-vacuity: a nonzero constant reference placed inside the cube -/

/-- The cube centre, the placement point of the non-vacuity witness. -/
def cubeCentre : Space := WithLp.toLp 2 (fun _ : Fin 3 => (1 / 2 : ℝ))

/-- The quarter-ball around the cube centre has its closure inside the open
fundamental cube; this discharges the geometric premise concretely. -/
theorem closure_ball_cubeCentre :
    closure (ball cubeCentre (1 / 4 : ℝ)) ⊆ interior fundamentalCube := by
  intro y hy
  have hyc : y ∈ closedBall cubeCentre (1 / 4 : ℝ) := closure_ball_subset_closedBall hy
  have hnorm : ‖y - cubeCentre‖ ≤ 1 / 4 := mem_closedBall_iff_norm.mp hyc
  rw [interior_fundamentalCube]
  intro i
  have hcoord : ‖(y - cubeCentre) i‖ ≤ 1 / 4 :=
    le_trans (PiLp.norm_apply_le (y - cubeCentre) i) hnorm
  have hval : (y - cubeCentre) i = y i - 1 / 2 := rfl
  rw [hval, Real.norm_eq_abs, abs_le] at hcoord
  exact ⟨by linarith [hcoord.1], by linarith [hcoord.2]⟩

theorem nonvacuous_energy :
    ∃ (v : SpaceTimeField) (θ : Space → ℝ) (η : ℝ → ℝ) (O : Set Space) (θR ε₀ : ℝ)
      (hv : ContDiff ℝ ∞ v) (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
      (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η),
      v ≠ 0 ∧ 0 < ε₀ ∧
      (∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0) ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v cubeCentre 1 θ η O θR ε₀).ε₀, ∀ t : ℝ,
        MemLp (torusLift (fun x : Space =>
            (correctionData v cubeCentre 1 θ η O θR ε₀).correction ε (t, x))) 2
          periodicTorusMeasure) ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v cubeCentre 1 θ η O θR ε₀).ε₀, ∀ t : ℝ,
        MemLp (torusLift (fun x : Space =>
            spatialGradient
              ((correctionData v cubeCentre 1 θ η O θR ε₀).correction ε) t x)) 2
          periodicTorusMeasure) ∧
      0 ≤ energyConst hv cubeCentre 1 hθ hη hθc hηc ∧
      (∀ ε ∈ Ioc (0 : ℝ) (correctionData v cubeCentre 1 θ η O θR ε₀).ε₀,
        energyENormT 1 ((correctionData v cubeCentre 1 θ η O θR ε₀).correction ε) ≤
          ENNReal.ofReal
            (energyConst hv cubeCentre 1 hθ hη hθc hηc * ε ^ ((3 : ℝ) / 2))) := by
  obtain ⟨θR, θ, O, hθR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  obtain ⟨ε₁, hε₁pos, _hεtime, hεspace₁⟩ :=
    exists_threshold hθR (by norm_num : (0 : ℝ) < 1 / 4)
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1)
  let v : SpaceTimeField := fun _ => coordinateVector 0
  have hv : ContDiff ℝ ∞ v := contDiff_const
  have hvdiv : ∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0 := by
    intro t x
    simp [spatialDivergence, spatialDerivative, v]
  have hvne : v ≠ 0 := by
    intro h
    have h0 := congrFun h ((0 : ℝ), (0 : Space))
    simp only [v, Pi.zero_apply] at h0
    have hc : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [h0]; rfl
    simp [coordinateVector] at hc
  refine ⟨v, θ, η, O, θR, min 1 ε₁, hv, hθsm, hηsm, hθcs, hηcs, hvne,
    lt_min one_pos hε₁pos, hvdiv, ?_, ?_, ?_, ?_⟩
  · exact correction_slice_memLp hv cubeCentre 1 O θR (min 1 ε₁) hθsm hηsm hθcs hηcs
      hθsupp hηsupp
  · exact correction_gradient_memLp hv cubeCentre 1 O θR (min 1 ε₁) hθsm hηsm hθcs hηcs
      hθsupp hηsupp
  · exact energyConst_nonneg hv cubeCentre 1 hθsm hηsm hθcs hηcs
  · exact correction_energy_bound hv cubeCentre 1 O hθsm hηsm hθcs hηcs hθsupp hηsupp
      closure_ball_cubeCentre (min_le_left _ _)
      (fun ε hε => hεspace₁ ε ⟨hε.1, hε.2.trans (min_le_right _ _)⟩)

end NSFormalization.Section3.T17.Probe

#print axioms NSFormalization.Section3.T17.Probe.field_correction_slice_memLp
#print axioms NSFormalization.Section3.T17.Probe.field_correction_gradient_memLp
#print axioms NSFormalization.Section3.T17.Probe.field_correction_energy_bound
#print axioms NSFormalization.Section3.T17.Probe.hcube_of_placement
#print axioms NSFormalization.Section3.T17.Probe.fields_at_placement
#print axioms NSFormalization.Section3.T17.Probe.closure_ball_cubeCentre
#print axioms NSFormalization.Section3.T17.Probe.nonvacuous_energy
