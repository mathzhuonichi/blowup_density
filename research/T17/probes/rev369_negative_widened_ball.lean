import NSFormalization.Section3.T17.LatticeDeriv

namespace NSFormalization.Section3.T17.Rev369Negative
open Set Metric NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement

example {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hs : ∀ t y, w (t, y) ≠ 0 → y ∈ ball x₀ ρ) (hr : r + ρ ≤ 2)
    {t : ℝ} {x : Space} (hx : x ∈ ball x₀ r) (n : ℕ) (u : Fin n → SpaceTime) :
  ‖iteratedFDeriv ℝ n (latticeLift w) (t,x) u‖ =
    ‖iteratedFDeriv ℝ n w (t,x) u‖ := by
  exact latticeLift_iteratedFDeriv_eq hs hr hx n u

end NSFormalization.Section3.T17.Rev369Negative
