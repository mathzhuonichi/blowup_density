import NSFormalization.Section3.T12.CutoffGagliardo

noncomputable section

namespace NSFormalization.Section3.T12

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)

/- This deliberately strengthens the main statement by halving its constant.
The existing proof must not typecheck against this mutated conclusion. -/
example (v : SpatialField) (hv : SmoothPeriodicT v) (hmean : IsMeanZeroT v) :
    dotHomogeneousENorm (1 / 2) (cutoffMul v)
      ≤ ENNReal.ofReal (cutoffGagliardoConst / 2)
        * (eLpNorm v 2 (volume.restrict fundamentalCube)
            + periodicHomogeneousENorm (1 / 2) v) :=
  cutoff_gagliardo_half v hv hmean

end NSFormalization.Section3.T12
