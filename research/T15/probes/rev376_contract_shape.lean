import NSFormalization.Section3.T15.Placement

namespace NSFormalization.Section3.T15

open Set NavierStokes.ProblemStatement

/- Reviewer shape check: the PacketAPI field is the full
   CompactPositiveTimeSupport clause, not merely HasCompactSupport.  Passing it
   verbatim to the shipped force theorem should therefore fail at its third
   argument; the consumer currently has to project `.1` (as in placement_closes).
-/
example {f : VelocityField} {x₀ : Space} {T ε : ℝ} {Kstar : Set Space}
    (hε : 0 < ε) (hKstar_compact : IsCompact Kstar)
    (hf : NavierStokesR3.ProblemStatement.CompactPositiveTimeSupport f)
    (hforce_proj : ∀ t : ℝ, ∀ x : Space, (t, x) ∈ tsupport f → x ∈ Kstar)
    (t : ℝ) :
    tsupport (fun x : Space => scaledForce f x₀ T ε (t, x)) ⊆
      (fun y : Space => x₀ + ε • y) '' Kstar := by
  exact scaledForce_tsupp_subset hε hKstar_compact hf hforce_proj t

end NSFormalization.Section3.T15
