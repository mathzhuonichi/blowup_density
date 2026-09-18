import NSFormalization.Section3.T12.GradientLSix
noncomputable section
namespace NSFormalization.Section3.T12
open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open scoped ENNReal
-- Substantive mutation: replace the uniform positive Csix by zero.
example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicLpENorm 6 (gradientTensor v) ≤
        ENNReal.ofReal (0 : ℝ) * periodicLpENorm 2 (laplacian v) :=
  gradientLSix
end NSFormalization.Section3.T12
