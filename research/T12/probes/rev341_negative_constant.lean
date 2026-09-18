import NSFormalization.Section3.T12.FourierEmbeddings

/- Negative review probe: changing the claimed Laplacian constant is substantive.
   The original theorem cannot discharge this altered-constant field. -/

noncomputable section

namespace NSFormalization.Section3.T12

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10
open scoped ENNReal

example :
    ∀ v : SpatialField, SmoothPeriodicT v → IsMeanZeroT v →
      periodicSobolevENorm 2 v ≤
        ENNReal.ofReal (hTwoConst + 1) * periodicLpENorm 2 (laplacian v) := by
  simpa using hTwo_le_laplacian

end NSFormalization.Section3.T12
