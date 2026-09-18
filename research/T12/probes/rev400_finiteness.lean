import NSFormalization.Section3.T12.GradientLSix
noncomputable section
namespace NSFormalization.Section3.T12
open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal
-- Positive control: exact API field and genuine finite right-hand side.
example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) :=
  gradientLSix
example {v : SpatialField} (hv : SmoothPeriodicT v) :
    periodicLpENorm 2 (laplacian v) < ⊤ :=
  (memLp_torusLift_vector (contDiff_lap hv.1).continuous 2).2
example {v : SpatialField} (hv : SmoothPeriodicT v) :
    ENNReal.ofReal Csix * periodicLpENorm 2 (laplacian v) < ⊤ :=
  ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (memLp_torusLift_vector (contDiff_lap hv.1).continuous 2).2
end NSFormalization.Section3.T12
