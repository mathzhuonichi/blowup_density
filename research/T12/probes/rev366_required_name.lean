import NSFormalization.Section3.T12.HaarCube

namespace NSFormalization.Section3.T12
open Set MeasureTheory
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open scoped ENNReal

/-- The principal finite-exponent specialization required by U1. -/
example (v : NavierStokes.ProblemStatement.Space → ℝ)
    (hv : IsPeriodicSpatial v) :
    eLpNorm (torusLift v) 3 periodicTorusMeasure =
      eLpNorm v 3 (volume.restrict fundamentalCube) := by
  exact eLpNorm_torusLift_eq_restrict v hv 3

end NSFormalization.Section3.T12
