import Contracts.V1.MeanZeroCalculus
import NSFormalization.Section3.T12.GradientLSix
open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open scoped ENNReal BigOperators
namespace NSFormalization.Section3.T12
example (v : SpatialField) (hv : SmoothPeriodicT v) (hm : IsMeanZeroT v) :
    periodicLpENorm 6 (gradientTensor v) ≤
      ENNReal.ofReal 0 * periodicLpENorm 2 (laplacian v) := by
  exact gradientLSix v hv
end NSFormalization.Section3.T12
