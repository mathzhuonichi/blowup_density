import NSFormalization.Section3.T20.CriticalTrilinear
open NSFormalization.Section3.T20
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NavierStokes.PeriodicIntegration
open scoped ENNReal BigOperators
-- Substantive mutation: replace the squared order-3/2 factor by the unsquared factor.
example (v Lv : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v)
    (hthree : MemPeriodicHomogeneous (3 / 2) v)
    (hL : IsPeriodicLambda v Lv) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦ (inner ℝ (advection (lift v) 0 x) (Lv x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      criticalTrilinearConst * (periodicHomogeneousENorm (1 / 2) v).toReal *
        (periodicHomogeneousENorm (3 / 2) v).toReal := by
  exact criticalTrilinear v Lv hv hhalf hthree hL
