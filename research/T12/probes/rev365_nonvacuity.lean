import NSFormalization.Section3.T12.Cutoff

/- Positive review probe: the plateau theorem has an explicit inhabited
   instance, so the cube condition is not empty/vacuous. -/

noncomputable section

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T13
open NSFormalization.Section3.T12
open NSFormalization.Section4.A02 (SpatialField MemHInfty)

example : (0 : Space) ∈ fundamentalCube := by
  intro i
  simp

example : cutoff (0 : Space) = 1 := by
  apply cutoff_eq_one
  intro i
  simp

def rev365ConstantField : SpatialField := fun _ => coordinateVector 0

example : cutoffMul rev365ConstantField (0 : Space) = coordinateVector 0 := by
  apply cutoffMul_eq_on_cube
  intro i
  simp

example : cutoffMul rev365ConstantField (0 : Space) ≠ 0 := by
  rw [show cutoffMul rev365ConstantField (0 : Space) = coordinateVector 0 by
    apply cutoffMul_eq_on_cube
    intro i
    simp]
  simp [coordinateVector]

example : MemHInfty (cutoffMul rev365ConstantField) := by
  apply memHInfty_cutoffMul
  exact contDiff_const
