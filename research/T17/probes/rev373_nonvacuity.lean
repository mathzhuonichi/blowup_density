import NSFormalization.Section3.T17.Transport

open Set Metric
open NavierStokes NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 (IsPeriodicOn)
open NSFormalization.Section3.T16 (latticeLift)
open NSFormalization.Section3.T17
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Paper1.CorrectionProfile (physicalCorrection)
open scoped ContDiff

noncomputable section

def rev373V : SpaceTimeField := fun _ => EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

example : rev373V ≠ 0 := by
  intro h
  have h0 : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) = (0 : Space) :=
    congrFun h (0, 0)
  have hn : ‖EuclideanSpace.single (0 : Fin 3) (1 : ℝ)‖ = 0 := by rw [h0, norm_zero]
  simp at hn

example :
    correctionForce 1 rev373V
        (correctionData rev373V 0 1 (fun _ => 0) (fun _ => 0) univ 0 1) (1 / 4)
      = latticeLift (NSFormalization.Source.correctionForce 1 rev373V
          (physicalCorrection rev373V 0 1 (fun _ => 0) (fun _ => 0) (1 / 4))) := by
  apply force_eq (δ := 1) (r := 1 / 4)
  · intro t _ x i
    rfl
  · exact contDiff_const.contDiffOn
  · exact contDiff_const
  · exact contDiff_const
  · exact HasCompactSupport.zero
  · exact HasCompactSupport.zero
  · simp
  · simp
  · norm_num
  · norm_num
  · norm_num
  · norm_num

end
