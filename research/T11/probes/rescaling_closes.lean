import NSFormalization.Section3.T11.Rescaling

/-! Exact target-shape and non-vacuity probe for T11/U4. -/

noncomputable section

namespace NSFormalization.Section3.T11.RescalingProbe

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar IsSolenoidal)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open scoped ContDiff

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT := by
  exact scaled_classes

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f := by
  exact inverse_identities

/-- The class-preservation theorem applies to a genuinely nonzero periodic
datum, and its explicit scaled datum remains nonzero. -/
example :
    ∃ (a : SpatialField) (f : SpaceTimeField),
      a ∈ initialClassT ∧ f ∈ forceClassT ∧
        unitViscosityInitialT 2 a ∈ initialClassT ∧
        unitViscosityForceT 2 f ∈ forceClassT ∧
        unitViscosityInitialT 2 a ≠ 0 := by
  let c : Space := coordinateVector 0
  let a : SpatialField := fun _ ↦ c
  let f : SpaceTimeField := 0
  have ha : a ∈ initialClassT := by
    refine ⟨contDiff_const, fun _ _ ↦ rfl, ?_⟩
    intro x
    simp [a, spatialDivergence, spatialDerivative]
  have hf : f ∈ forceClassT := by
    refine ⟨contDiff_const, fun _ _ _ _ ↦ rfl,
      ∅, isCompact_empty, empty_subset _, ?_⟩
    simp [f]
  obtain ⟨ha_scaled, hf_scaled⟩ := scaled_classes 2 (by norm_num) a ha f hf
  refine ⟨a, f, ha, hf, ha_scaled, hf_scaled, ?_⟩
  intro hzero
  have hvalue := congrFun hzero (0 : Space)
  have hcomponent := congrArg (fun v : Space ↦ v (0 : Fin 3)) hvalue
  norm_num [unitViscosityInitialT, a, c, coordinateVector] at hcomponent

end NSFormalization.Section3.T11.RescalingProbe
