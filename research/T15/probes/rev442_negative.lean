import NSFormalization.Section3.T15.Blowup

/-!
Reviewer mutation: shift the asserted blow-up time from `place.T` to
`place.T + 1`.  The lane theorem must not prove this stronger, different
claim.
-/

noncomputable section

namespace NSFormalization.Section3.T15

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling

variable {u f : VelocityField} {p : PressureField} {K : Set Space}
variable (hK : IsCompact K)
variable (hu : ∀ t ∈ Ico (0 : ℝ) 1,
  tsupport (fun x : Space => u (t, x)) ⊆ K)
variable (hspeed : SpeedUnboundedAtOne u)
variable (place : PlacementData u p f K)

example : ∀ ε ∈ Ioc (0 : ℝ) place.ε₀,
    SpeedUnboundedAt (place.T + 1)
      (periodizedScaledVelocity u place.x₀ place.T ε) := by
  exact unboundedSpeed hK hu hspeed place

end NSFormalization.Section3.T15
