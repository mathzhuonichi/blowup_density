import NSFormalization.Section4.R43.Trilinear

open Set NavierStokes.ProblemStatement
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField ClassicalSolutionR MemForceR)

namespace NSFormalization.Section4.R43

set_option autoImplicit false in
example {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    {w : ClassicalSolutionR ν a f T} {hf : MemForceR f}
    (hcrit : CriticalDatumPath w hf)
    (hbridge : CriticalAdvectionLpBridge hcrit) :
    CriticalTrilinearEstimate (C₀ := trilinearConst / 2) hcrit := by
  exact criticalTrilinearEstimate_of_hcrit hcrit hbridge

end NSFormalization.Section4.R43
