import NSFormalization.Section3.T17.LatticeDeriv

namespace NSFormalization.Section3.T17.Review369Api
open Set Metric
open NSFormalization.Section3.T10
open NSFormalization.Section3.T16
open NSFormalization.Section4.A02 (SpaceTimeField)
open NavierStokes.ProblemStatement

/- The brief names the arbitrary-z existential theorem
   `latticeLift_iteratedFDeriv_eq`.  This probe records whether that exact
   public name has the requested type. -/
example {w : SpaceTimeField} {x₀ : Space} {ρ r : ℝ}
    (hslice : ∀ (t : ℝ) (y : Space), w (t, y) ≠ 0 → y ∈ ball x₀ ρ)
    (hρr : r + ρ ≤ 1) (hlt : ρ < r)
    (z : SpaceTime) (n : ℕ) (u : Fin n → SpaceTime) :
    ∃ k : PeriodicFrequency,
      ‖iteratedFDeriv ℝ n (latticeLift w) z u‖ =
        ‖iteratedFDeriv ℝ n w (z - (0, latticeVector k)) u‖ := by
  exact latticeLift_iteratedFDeriv_eq hslice hρr hlt z n u

end NSFormalization.Section3.T17.Review369Api
