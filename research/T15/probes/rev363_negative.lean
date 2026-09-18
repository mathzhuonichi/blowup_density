import NSFormalization.Section3.T15.ParsevalZero
open MeasureTheory
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12 (SmoothPeriodicT)
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T15
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal
noncomputable section
example (z : SpatialField) (hz : SmoothPeriodicT z) :
    periodicSobolevENorm 0 z = eLpNorm (torusLift z) 2 periodicTorusMeasure + 1 := by
  rw [periodicSobolevENorm_zero_eq z hz]
