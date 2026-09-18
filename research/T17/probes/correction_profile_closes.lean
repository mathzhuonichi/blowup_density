import NSFormalization.Section3.T16.Assembly
import NSFormalization.Section3.T17.CorrectionProfile

/-!
# Probe: the six `CorrectionAPI` correction-profile fields close on the T17 U3 module

Part A restates each of the six fields of `research/T17/Spec.lean:784-830`
(substitution ruling of the lead: the Spec threads `place : PlacementData P`;
`PlacementData` needs `Contracts.V1.PacketAPI`, unreachable from `formalization/`,
so `place.x₀ ↦ x₀`, `place.T ↦ T`, the canonical bare-`(x₀,T)` T16 spelling, stands
and the assembly instantiates `place.x₀`/`place.T`) and closes each by `exact`.

Part B is a genuine non-vacuity instance at a **nonzero constant divergence-free
periodic** reference `constRef = fun _ => coordinateVector 0` (periodicity and
divergence-freeness are proved, not asserted in a comment):

* `nonvacuous_correction_profile_fields` discharges the five cutoff-data-only
  fields with T16's Urysohn cutoff data (`exists_originCutoff`/`exists_timeCutoff`);
* `nonvacuous_correction_profile_identity` builds a real `LocalPotentialAPI`
  witness through T16's `localPotential` assembly (`Section3/T16/Assembly.lean`,
  #330) and instantiates `correction_profile_identity` on it.
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
open NSFormalization.Section3.T10 (IsPeriodicOn)

/-- A nonzero constant reference velocity. -/
def constRef : SpaceTimeField := fun _ => coordinateVector 0

theorem constRef_ne_zero : constRef ≠ 0 := by
  intro h
  have := congrFun h ((0 : ℝ), (0 : Space))
  simp only [constRef, Pi.zero_apply] at this
  have h0 : (coordinateVector (0 : Fin 3)) (0 : Fin 3) = 0 := by rw [this]; rfl
  simp [coordinateVector] at h0

theorem constRef_smooth : ContDiff ℝ ∞ constRef := contDiff_const

/-- A constant field is unit-periodic (proved, not asserted). -/
theorem constRef_periodic : IsPeriodicOn univ constRef := fun _ _ _ _ => rfl

/-- A constant field is divergence-free (proved, not asserted). -/
theorem constRef_divergence_free : ∀ t : ℝ, ∀ x : Space,
    spatialDivergence constRef t x = 0 := by
  intro t x
  simp [spatialDivergence, spatialDerivative, constRef]

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

/-- Concrete non-vacuity of `correction_profile_identity`: a real
`LocalPotentialAPI` witness for the nonzero constant divergence-free periodic
reference, built by T16's `localPotential` assembly, on which the identity field
is instantiated.  `U := 0`, `K := ∅`, `x₀ := 0`, `r := 1/4`, `T := δ := 1`. -/
theorem nonvacuous_correction_profile_identity :
    ∃ (v U : SpaceTimeField) (K : Set Space) (x₀ : Space) (r T δ : ℝ)
      (D : CutoffData),
      v ≠ 0 ∧ IsPeriodicOn univ v ∧
      (∀ t : ℝ, ∀ x : Space, spatialDivergence v t x = 0) ∧
      LocalPotentialAPI v U K x₀ r T δ D ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ z ∈ fixedProfileCylinder D,
        D.correction ε (correctionChartPoint x₀ T ε z) =
          rescaledCorrectionProfile v x₀ T ε D z) := by
  have hUsupp : ∀ t ∈ Ioo (0 : ℝ) 1,
      tsupport (fun x => (0 : SpaceTimeField) (t, x)) ⊆ (∅ : Set Space) := by
    intro t _; simp [tsupport]
  obtain ⟨D, hpot⟩ :=
    localPotential constRef 0 (∅ : Set Space) 0 (1 / 4) 1 1
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) isCompact_empty
      constRef_periodic constRef_smooth.contDiffOn
      (fun t _ x _ => constRef_divergence_free t x) hUsupp
  exact ⟨constRef, 0, ∅, 0, 1 / 4, 1, 1, D, constRef_ne_zero, constRef_periodic,
    constRef_divergence_free, hpot,
    correction_profile_identity constRef_smooth hpot⟩

end NonVacuity

end NSFormalization.Section3.T17.Probe
