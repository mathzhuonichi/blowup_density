import NSFormalization.Paper1.PeriodicPicardTwoStep
import NSFormalization.Paper1.PeriodicPicardDuhamelContraction

noncomputable section
namespace NSFormalization.Paper1

/-- Final conditional wrapper from the supplied two-step error recurrence to the
geometric orbit estimate. -/
theorem picard_two_step_orbit_error_bound
    {E : Type*} [NormedAddCommGroup E]
    (C : PicardContractionContract E) (x : ℕ → E) (xstar : E)
    (e : ℕ → ℝ) (hx0 : x 0 ∈ C.ball) (hxstar : xstar ∈ C.ball)
    (horbit : ∀ n, x (n + 1) = C.map (x n))
    (hfix : C.map xstar = xstar)
    (he : ∀ n, e n = ‖x n - xstar‖)
    (hstep : ∀ n, e (n + 1) ≤ C.q * e n) (n : ℕ) :
    ‖x n - xstar‖ ≤ C.q ^ n * ‖x 0 - xstar‖ := by
  exact picard_duhamel_two_step_geometric C x xstar e hx0 hxstar horbit hfix he hstep n

end NSFormalization.Paper1
