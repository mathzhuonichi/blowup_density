import NSFormalization.Section3.T17.CorrectionProfile

/-!
# Probe: the six `CorrectionAPI` correction-profile fields close on the T17 U3 module

Part A restates each of the six fields of `research/T17/Spec.lean:784-830`
**token-for-token** (only substitution: the Spec threads `place : PlacementData P`,
here read through its two used fields `place.x₀ ↦ x₀`, `place.T ↦ T`, exactly as
canonical T16 uses bare `x₀ : Space`, `T : ℝ`) and closes each by `exact`.

Part B is a non-vacuity instance: a nonzero smooth (divergence-free) reference `v`
(a constant field) with T16's cutoff data (`exists_originCutoff`/`exists_timeCutoff`),
discharging the hypotheses of the five fields that depend only on the cutoff data.
The sixth field, `correction_profile_identity`, is over the abstract
`D.correction ε`; a *concrete* non-vacuity witness for it needs a full
`LocalPotentialAPI` (T16's `localPotential` assembly, lane 358, not in this
worktree).  Its field theorem is fully proved here (Part A) from the
`LocalPotentialAPI` hypothesis the `CorrectionAPI` supplies.
-/

noncomputable section

namespace NSFormalization.Section3.T17.Probe

open Set MeasureTheory
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T16 (CutoffData LocalPotentialAPI)
open NSFormalization.Section4.A02 (SpaceTimeField)
open scoped ContDiff Topology

/-! ## Part A — the six Spec fields, restated and closed by `exact` -/

section Fidelity

variable {v U : SpaceTimeField} {K : Set Space} {x₀ : Space} {r T δ : ℝ} {D : CutoffData}

/-- `Spec.lean:784-786`: `correction_profile_smooth`. -/
theorem field_correction_profile_smooth (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      ContDiffOn ℝ ∞ (rescaledCorrectionProfile v x₀ T ε D)
        (fixedProfileCylinder D) :=
  correction_profile_smooth hv x₀ T D hθ hη

/-- `Spec.lean:789-790`: `correction_profile_support`. -/
theorem field_correction_profile_support (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθsupp : tsupport D.θ ⊆ Metric.ball (0 : Space) D.θRadius)
    (hηsupp : tsupport D.η ⊆ Ioo (-2 : ℝ) 2) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      tsupport (rescaledCorrectionProfile v x₀ T ε D) ⊆ fixedProfileCylinder D :=
  correction_profile_support hv x₀ T D hθ hη hθsupp hηsupp

/-- `Spec.lean:793`: `correctionProfileConst` (data). -/
def field_correctionProfileConst (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η) : ℕ → ℝ :=
  correctionProfileConst hv x₀ T hθ hη hθc hηc

/-- `Spec.lean:796`: `correctionProfileConst_nonneg`. -/
theorem field_correctionProfileConst_nonneg (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η) :
    ∀ k, 0 ≤ field_correctionProfileConst (x₀ := x₀) (T := T) hv hθ hη hθc hηc k :=
  correctionProfileConst_nonneg hv x₀ T hθ hη hθc hηc

/-- `Spec.lean:799-802`: `correction_profile_uniform`. -/
theorem field_correction_profile_uniform (hv : ContDiff ℝ ∞ v)
    (hθ : ContDiff ℝ ∞ D.θ) (hη : ContDiff ℝ ∞ D.η)
    (hθc : HasCompactSupport D.θ) (hηc : HasCompactSupport D.η) (hε₀ : D.ε₀ ≤ 1) :
    ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v x₀ T ε D) z‖ ≤
        field_correctionProfileConst (x₀ := x₀) (T := T) hv hθ hη hθc hηc k :=
  correction_profile_uniform hv x₀ T D hθ hη hθc hηc hε₀

/-- `Spec.lean:827-830`: `correction_profile_identity`.  Over the abstract
`D.correction ε`, discharged from the `LocalPotentialAPI` witness the
`CorrectionAPI` carries as its `potential` field. -/
theorem field_correction_profile_identity (hv : ContDiff ℝ ∞ v)
    (hpot : LocalPotentialAPI v U K x₀ r T δ D) :
    ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
      D.correction ε (correctionChartPoint x₀ T ε z) =
        rescaledCorrectionProfile v x₀ T ε D z :=
  correction_profile_identity hv hpot

end Fidelity

/-! ## Part B — non-vacuity: a constant reference with T16 cutoff data -/

section NonVacuity

open NSFormalization.Section3.T16

/-- A nonzero constant reference velocity; smooth and divergence-free. -/
def constRef : SpaceTimeField := fun _ => coordinateVector 0

theorem constRef_ne_zero : constRef ≠ 0 := by
  intro h
  have := congrFun h ((0 : ℝ), (0 : Space))
  simp only [constRef, Pi.zero_apply] at this
  have h0 : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [this]; rfl
  simp [coordinateVector] at h0

theorem constRef_smooth : ContDiff ℝ ∞ constRef := contDiff_const

/-- Concrete cutoff data built from the T16 Urysohn cutoffs. -/
theorem nonvacuous_correction_profile_fields :
    ∃ (v : SpaceTimeField) (D : CutoffData),
      v ≠ 0 ∧ ContDiff ℝ ∞ v ∧ D.ε₀ ≤ 1 ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          ContDiffOn ℝ ∞ (rescaledCorrectionProfile v (0 : Space) 1 ε D)
            (fixedProfileCylinder D)) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          tsupport (rescaledCorrectionProfile v (0 : Space) 1 ε D) ⊆
            fixedProfileCylinder D) ∧
      (∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
        ∀ k : ℕ, ∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
          ‖iteratedFDeriv ℝ k (rescaledCorrectionProfile v (0 : Space) 1 ε D) z‖ ≤
            C k) := by
  obtain ⟨R, θ, O, hR, hθsm, hθcs, hθsupp, hOopen, hKO, hθone, hθrange⟩ :=
    exists_originCutoff (K := (∅ : Set Space)) isCompact_empty
  obtain ⟨η, hηsm, hηcs, hηrange, hηone, hηsupp⟩ := exists_timeCutoff
  refine ⟨constRef,
    { θ := θ, η := η, plateau := O, θRadius := R, ε₀ := 1,
      potential := 0, correction := fun _ => 0 },
    constRef_ne_zero, constRef_smooth, le_refl 1, ?_, ?_, ?_⟩
  · exact correction_profile_smooth constRef_smooth 0 1 _ hθsm hηsm
  · exact correction_profile_support constRef_smooth 0 1 _ hθsm hηsm hθsupp hηsupp
  · exact ⟨correctionProfileConst constRef_smooth 0 1 hθsm hηsm hθcs hηcs,
      correctionProfileConst_nonneg constRef_smooth 0 1 hθsm hηsm hθcs hηcs,
      correction_profile_uniform constRef_smooth 0 1 _ hθsm hηsm hθcs hηcs (le_refl 1)⟩

end NonVacuity

end NSFormalization.Section3.T17.Probe
