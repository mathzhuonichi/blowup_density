import NSFormalization.Section4.A04.H1Bridges
import NSFormalization.Section4.A05.SmoothJets

/-!
Intentional failing reviewer probe for the lane-504/B1 handoff.

The first example has exactly the regularity exported for a classical velocity
slice (`SmoothL2`) but no compact-support hypothesis.  The second retains all
B0 arguments but uses B1's fixed whole-space coefficient `(2π)⁻²` instead of
the angular registered convention's coefficient `1`.
-/

noncomputable section

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped ContDiff

example {z : SpatialField} (hz : NSFormalization.Section4.A05.SmoothL2 z) :
    (sobolevENorm 1 z).toReal ^ 2 =
      NSFormalization.Section4.A04.l2EnergyR z +
        NSFormalization.Section4.A04.gradientEnergyR z := by
  exact NSFormalization.Section4.A04.sobolevENorm_one_toReal_sq_eq hz.contDiff

example {z : SpatialField} (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (sobolevENorm 1 z).toReal ^ 2 =
      NSFormalization.Section4.A04.l2EnergyR z +
        (1 / (2 * Real.pi) ^ 2) * NSFormalization.Section4.A04.gradientEnergyR z := by
  exact NSFormalization.Section4.A04.sobolevENorm_one_toReal_sq_eq hz hc
