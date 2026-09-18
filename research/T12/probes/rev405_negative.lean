import NSFormalization.Section3.T12.GradientLambdaL3
namespace NSFormalization.Section3.T12
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
example (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hm : MemPeriodicHomogeneous (3 / 2) v) (hL : IsPeriodicLambda v Lv) :
    periodicLpENorm 3 (gradientTensor v) + periodicLpENorm 3 Lv ≤
      ENNReal.ofReal (CcriticalThreeHalves - 1) * periodicHomogeneousENorm (3 / 2) v := by
  exact gradientLambdaCriticalL3 v Lv hv hm hL
end NSFormalization.Section3.T12
