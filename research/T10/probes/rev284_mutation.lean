import NSFormalization.Section3.T10.PhysicalBridge

noncomputable section

namespace NSFormalization.Section3.T10

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)

/-!
Reviewer negative probe: flip the sign of the reconstructed field.  Reusing the
real proof must fail because `mean_decomposition` reconstructs `z`, not `-z`.
-/

example :
    forall z : SpatialField, IsPeriodicSpatial z →
      Integrable (torusLift z) periodicTorusMeasure →
        (forall x : Space, constantPartT z x + meanZeroPartT z x = -z x) ∧
          IsMeanZeroT (meanZeroPartT z) := by
  exact mean_decomposition

end NSFormalization.Section3.T10
