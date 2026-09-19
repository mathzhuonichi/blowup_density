import NSFormalization.Section3.T23.Placement

/-!
# Reviewer mutation probe for T23 U1

This deliberately flips the strict inequality in the main temporal placement
field.  Reusing the production proof must fail: the proved direction is
`2 * ε ^ 2 < T`, not `T < 2 * ε ^ 2`.
-/

noncomputable section

namespace NSFormalization.Section3.T23.ReviewerMutation

open Set
open NavierStokes.ProblemStatement

example {u : VelocityField} {p : PressureField} {f : VelocityField}
    {K : Set Space} (place : DomainPlacementData u p f K) :
    ∀ ε ∈ Ioc (0 : ℝ) place.ε₀, place.T < 2 * ε ^ 2 := by
  exact place.eps_time

end NSFormalization.Section3.T23.ReviewerMutation
