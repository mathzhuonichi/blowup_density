import NSFormalization.Section3.T17.ForceProfile

/-!
# Probe: the six `CorrectionAPI` force-profile fields close on the T17 U4 module

Part A restates each of the six force-profile fields of
`research/T17/Spec.lean:805-837` **token-for-token** (only substitution: the
Spec threads `place : PlacementData P`, here read through its two used fields
`place.x₀ ↦ x₀`, `place.T ↦ T`, exactly as canonical T16 uses bare
`x₀ : Space`, `T : ℝ`) and closes each by `exact`.

The **sixth** field, `force_profile_identity`, is stated in the Spec over
`correctionForce ν v D ε` (the T17 force operator built from the *abstract*
`D.correction ε`, lane 373's `Transport.lean` spelling).  With that module now on
the base, it is closed in **Spec form** (`field_force_profile_identity` below,
from a `LocalPotentialAPI` witness — exactly as lane 370's probe closes
`correction_profile_identity`).  The chart-force variant
(`field_force_profile_identity_chartForce`) is also kept.

Part B is a non-vacuity instance: a nonzero smooth reference `v` (a constant
field) with T16's cutoff data (`exists_originCutoff`/`exists_timeCutoff`),
discharging the hypotheses of all six fields (the chart-force identity needs
only `hv, hθ, hη`, no `LocalPotentialAPI`, so it is discharged here too).
-/

noncomputable section

namespace NSFormalization.Section3.T17.ForceProbe

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16 (CutoffData LocalPotentialAPI)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open scoped ContDiff Topology

/-! ## Part A — the six Spec fields, restated and closed by `exact` -/

section Fidelity

variable {ν : ℝ} {v U : SpaceTimeField} {K : Set Space} {x₀ : Space} {r T δ : ℝ}
  {D : CutoffData}

/-- `Spec.lean:805-808`: `force_profile_smooth`. -/
theorem field_force_profile_smooth (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      ContDiffOn ℝ ∞ (rescaledForceProfile ν v x₀ T ε D)
        (fixedProfileCylinder D) :=
  force_profile_smooth ν hv x₀ T D hθ hη

/-- `Spec.lean:810-811`: `force_profile_support`. -/
theorem field_force_profile_support (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθsupp : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius)
    (hηsupp : tsupport D.η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      tsupport (rescaledForceProfile ν v x₀ T ε D) ⊆ fixedProfileCylinder D :=
  force_profile_support ν hv x₀ T D hθ hη hθsupp hηsupp

/-- `Spec.lean:814`: `forceProfileConst` (data). -/
def field_forceProfileConst (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η) : ℕ → ℝ :=
  forceProfileConst ν hv x₀ T hθ hη hθc hηc

/-- `Spec.lean:817`: `forceProfileConst_nonneg`. -/
theorem field_forceProfileConst_nonneg (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η) :
    ∀ k, 0 ≤ field_forceProfileConst (ν := ν) (x₀ := x₀) (T := T) hv hθ hη hθc hηc k :=
  forceProfileConst_nonneg ν hv x₀ T hθ hη hθc hηc

/-- `Spec.lean:820-823`: `force_profile_uniform`. -/
theorem field_force_profile_uniform (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η) (hε₀ : D.ε₀ ≤ 1) :
    ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledForceProfile ν v x₀ T ε D) z‖ ≤
        field_forceProfileConst (ν := ν) (x₀ := x₀) (T := T) hv hθ hη hθc hηc k :=
  force_profile_uniform ν hv x₀ T D hθ hη hθc hηc hε₀

/-- `Spec.lean:834-837`: `force_profile_identity`, **Spec form** — the LHS is the
abstract-correction force `correctionForce ν v D ε (chart)` (lane 373's
`Transport.correctionForce`).  Closed from a `LocalPotentialAPI` witness the
`CorrectionAPI` carries as its `potential` field, exactly as lane 370's probe
closes `correction_profile_identity`. -/
theorem field_force_profile_identity (hv : ContDiff ℝ ∞ v)
    (hpot : LocalPotentialAPI v U K x₀ r T δ D) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      correctionForce ν v D ε (correctionChartPoint x₀ T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z :=
  force_profile_identity ν hv hpot

/-- The same identity's **chart-force form**
`Source.correctionForce ν v (physicalCorrection …) (chart)`, needing only
`hv, hθ, hη` (no `LocalPotentialAPI`). -/
theorem field_force_profile_identity_chartForce (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      Source.correctionForce ν v (physicalCorrection v x₀ T D.θ D.η ε)
          (correctionChartPoint x₀ T ε z) =
        (ε ^ 2)⁻¹ • rescaledForceProfile ν v x₀ T ε D z :=
  physicalForce_eq_rescaledForceProfile ν hv x₀ T D hθ hη

end Fidelity

/-! ## Part B — non-vacuity: a constant reference with T16 cutoff data -/

section NonVacuity

open NSFormalization.Section3.T16

/-- A nonzero constant reference velocity; smooth. -/
def constRef : SpaceTimeField := fun _ => coordinateVector 0

theorem constRef_ne_zero : constRef ≠ 0 := by
  intro h
  have := congrFun h ((0 : ℝ), (0 : Space))
  simp only [constRef, Pi.zero_apply] at this
  have h0 : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [this]; rfl
  simp [coordinateVector] at h0

theorem constRef_smooth : ContDiff ℝ ∞ constRef := contDiff_const

/-- All six force-profile fields are satisfiable at a nonzero constant reference
with T16 Urysohn cutoff data (the chart-force identity included). -/
theorem nonvacuous_force_profile_fields :
    ∃ (v : SpaceTimeField) (D : CutoffData),
      v ≠ 0 ∧ ContDiff ℝ ∞ v ∧ D.ε₀ ≤ 1 ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          ContDiffOn ℝ ∞ (rescaledForceProfile 1 v (0 : Space) 1 ε D)
            (fixedProfileCylinder D)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          tsupport (rescaledForceProfile 1 v (0 : Space) 1 ε D) ⊆
            fixedProfileCylinder D) ∧
      (∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
        ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
          ‖iteratedFDeriv ℝ k (rescaledForceProfile 1 v (0 : Space) 1 ε D) z‖ ≤
            C k) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
          Source.correctionForce 1 v (physicalCorrection v (0 : Space) 1 D.θ D.η ε)
              (correctionChartPoint (0 : Space) 1 ε z) =
            (ε ^ 2)⁻¹ • rescaledForceProfile 1 v (0 : Space) 1 ε D z) := by
  obtain ⟨R, θ, O, hR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  refine ⟨constRef,
    { θ := θ, η := η, plateau := O, θRadius := R, ε₀ := 1,
      potential := 0, correction := fun _ => 0 },
    constRef_ne_zero, constRef_smooth, le_refl 1, ?_, ?_, ?_, ?_⟩
  · exact force_profile_smooth 1 constRef_smooth 0 1 _ hθsm hηsm
  · exact force_profile_support 1 constRef_smooth 0 1 _ hθsm hηsm hθsupp hηsupp
  · exact ⟨forceProfileConst 1 constRef_smooth 0 1 hθsm hηsm hθcs hηcs,
      forceProfileConst_nonneg 1 constRef_smooth 0 1 hθsm hηsm hθcs hηcs,
      force_profile_uniform 1 constRef_smooth 0 1 _ hθsm hηsm hθcs hηcs (le_refl 1)⟩
  · exact physicalForce_eq_rescaledForceProfile 1 constRef_smooth 0 1 _ hθsm hηsm

end NonVacuity

end NSFormalization.Section3.T17.ForceProbe
