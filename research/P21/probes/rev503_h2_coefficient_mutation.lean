import NSFormalization.Section4.A04.H1Bridges

/-!
Intentional negative reviewer probe for lane 503.  The H² recurrence's
gradient coefficient is changed from `1` to `2`; replaying the shipped theorem
must fail at the conclusion, without dropping any argument.
-/

noncomputable section

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.D01 (sobolevENorm)
open scoped ContDiff

example {z : SpatialField} (hz : ContDiff ℝ ∞ z) (hc : HasCompactSupport z) :
    (sobolevENorm 2 z).toReal ^ 2 =
      (sobolevENorm 1 z).toReal ^ 2 +
        2 * NSFormalization.Section4.A04.gradientEnergyR z +
          NSFormalization.Section4.A04.hessianEnergyR z := by
  exact NSFormalization.Section4.A04.sobolevENorm_two_eq_one_add_gradient_hessian hz hc
