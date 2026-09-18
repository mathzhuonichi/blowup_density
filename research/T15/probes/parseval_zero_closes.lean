import NSFormalization.Section3.T15.ParsevalZero

noncomputable section

namespace NSFormalization.Section3.T15

open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NSFormalization.Section4.A02 (SpatialField)
open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal

/-! A concrete nonzero smooth periodic mode: the constant first coordinate. -/

def constantMode : SpatialField := fun _ ↦ coordinateVector 0

theorem constantMode_smoothPeriodic : SmoothPeriodicT constantMode := by
  refine ⟨contDiff_const, ?_⟩
  intro x j
  rfl

theorem constantMode_nonzero : constantMode ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Space)
  have hc : coordinateVector 0 ≠ (0 : Space) := by
    intro hc
    have hi := congrArg (fun y : Space => y 0) hc
    norm_num [coordinateVector] at hi
  exact hc h0

example :
    periodicSobolevENorm 0 constantMode =
      eLpNorm (torusLift constantMode) 2 periodicTorusMeasure :=
  periodicSobolevENorm_zero_eq constantMode constantMode_smoothPeriodic

end NSFormalization.Section3.T15
