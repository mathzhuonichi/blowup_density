import NSFormalization.Section3.T20.H1Trilinear

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T12
open NSFormalization.Section4.A02 (SpatialField)
open scoped ContDiff ENNReal BigOperators

/- A substantive mutation: replace the proved constant C₁ by C₁ - 1.
   The original proof term must fail by a genuine target mismatch. -/
example (v : SpatialField) (hv : SmoothPeriodicT v)
    (hhalf : MemPeriodicHomogeneous (1 / 2) v) :
    |∫ y : PeriodicTorus,
        torusLift (fun x ↦
          (inner ℝ (advection (lift v) 0 x) (laplacian v x) : ℝ)) y
          ∂periodicTorusMeasure| ≤
      (h1TrilinearConst - 1) *
          (periodicHomogeneousENorm (1 / 2) v).toReal * laplacianSqT v := by
  exact h1Trilinear v hv hhalf

end NSFormalization.Section3.T20
