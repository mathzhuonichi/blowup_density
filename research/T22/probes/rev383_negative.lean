import NSFormalization.Section3.T22.RestrictBridge

/-! Negative reviewer probe: flip the proved left inequality. -/

noncomputable section

namespace NSFormalization.Section3.T22.ReviewProbe

open Set
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Section3.T22
open NSFormalization.Section4.D01
open NSFormalization.Section4.A02 (SpatialField)

example {Ω : Set Space} {s : ℝ} {z : SpatialField} :
    sobolevENorm s (zeroExtension Ω z) ≤
      domainSobolevENorm Ω s (restrictField Ω z) := by
  exact domainSobolevENorm_le_sobolevENorm

end NSFormalization.Section3.T22.ReviewProbe
