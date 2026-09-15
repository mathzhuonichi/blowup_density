import NSFormalization.Section4.A01.ConstructorDivergence
import Euler.LpSmoothFieldAlgebra

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space coordinateVector spatialDivergence)
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerCylinderSobolev EulerPressureSpatialRegularity EulerLpTranslation
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.A01
open scoped ContDiff

#print axioms NSFormalization.Section4.A01.divergence_ae_of_cylinder
#print axioms NSFormalization.Section4.A01.divergence_of_cylinder_pointwise_of_contDiff

/-! Non-vacuity: the zero cylinder pair and zero smooth representative satisfy the a.e. theorem. -/
example :
    ∀ᵐ x ∂(volume : Measure Space), ∑ i : Fin 3,
      (fderiv ℝ (SmoothL2Field.zeroField : SmoothL2Field Space).field x
        (coordinateVector i)) i = 0 := by
  apply divergence_ae_of_cylinder (q := 0)
    (u := (0 : SobolevSpace 1 (0 + 1)))
    (U := (0 : EulerMeanSolenoidal.L2))
    (Z := (SmoothL2Field.zeroField : SmoothL2Field Space))
  · intro θ
    simp
  · change ordinaryLift 0 = valueOperator 1 1 0
    rw [map_zero, map_zero]
  · rw [show value 1 (0 : SobolevSpace 1 1) = 0 from map_zero (valueOperator 1 1)]
    exact Submodule.zero_mem _
  · exact (Lp.coeFn_zero Space 2 volume).symm

/-! The all-time c3 handoff is likewise inhabited by the zero cylinder pair and zero velocity. -/
example :
    ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Space,
      spatialDivergence (0 : SpaceTimeField) t x = 0 := by
  apply divergence_of_cylinder_pointwise_of_contDiff
    (u := (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 (0 + 1))))
    (U := (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)))
    (Z := fun _ => (SmoothL2Field.zeroField : SmoothL2Field Space))
    (velocity := (0 : SpaceTimeField))
  · intro t θ
    simp
  · intro t
    change ordinaryLift 0 = valueOperator 1 1 0
    rw [map_zero, map_zero]
  · intro t
    change value 1 (0 : SobolevSpace 1 1) ∈ divergenceFreeSpace 1 1 0
    rw [show value 1 (0 : SobolevSpace 1 1) = 0 from map_zero (valueOperator 1 1)]
    exact Submodule.zero_mem _
  · intro t
    exact (Lp.coeFn_zero Space 2 volume).symm
  · intro t
    exact (Lp.coeFn_zero Space 2 volume).symm
  · intro t ht
    exact contDiff_const
