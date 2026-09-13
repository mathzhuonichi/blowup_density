import NSFormalization.Paper1.PeriodicPicardContractionComposition
import NSFormalization.Paper1.PeriodicPicardDuhamelIteration

noncomputable section
namespace NSFormalization.Paper1

/-- Composition theorem: an explicitly supplied Duhamel error recurrence and an
explicit contractive orbit imply a geometric orbit error bound. -/
theorem picard_duhamel_orbit_error_geometric
    {E : Type*} [NormedAddCommGroup E]
    (C : PicardContractionContract E) (x : ℕ → E) (xstar : E)
    (e : ℕ → ℝ) (hx0 : x 0 ∈ C.ball) (hxstar : xstar ∈ C.ball)
    (horbit : ∀ n, x (n + 1) = C.map (x n))
    (hfix : C.map xstar = xstar)
    (he : ∀ n, e n = ‖x n - xstar‖)
    (hstep : ∀ n, e (n + 1) ≤ C.q * e n) (n : ℕ) :
    ‖x n - xstar‖ ≤ C.q ^ n * ‖x 0 - xstar‖ := by
  have hstep' : ∀ m, ‖x (m + 1) - xstar‖ ≤ C.q * ‖x m - xstar‖ := by
    intro m
    simpa [he (m + 1), he m] using hstep m
  exact C.iterate_error_bound x xstar hx0 hxstar horbit hfix n

end NSFormalization.Paper1
