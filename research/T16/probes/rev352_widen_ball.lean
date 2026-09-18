import NSFormalization.Section3.T16.LatticeLift

open Set Metric
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)

noncomputable section

/- Negative mutation: widen the locality hypothesis from `r + ρ ≤ 1` to
   `r + ρ ≤ 2`.  The existing proof must fail because the integer-translate
   separation argument needs the unit bound. -/
example {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 2) {t : ℝ} {x : Space} (hx : x ∈ ball x₀ r) :
    latticeLift w (t, x) = w (t, x) := by
  exact latticeLift_eq_of_ball hslice hρr hx
