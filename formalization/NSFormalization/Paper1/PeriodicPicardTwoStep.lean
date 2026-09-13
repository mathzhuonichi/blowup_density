import NSFormalization.Paper1.PeriodicPicardDuhamelContraction

noncomputable section
namespace NSFormalization.Paper1

/-- Two-step conditional composition: a Duhamel gain and scalar comparison
produce the recurrence required for geometric Picard orbit control. -/
theorem picard_duhamel_two_step_geometric
    {E : Type*} [NormedAddCommGroup E]
    (C : PicardContractionContract E) (x : ℕ → E) (xstar : E)
    (e : ℕ → ℝ) (hx0 : x 0 ∈ C.ball) (hxstar : xstar ∈ C.ball)
    (horbit : ∀ n, x (n + 1) = C.map (x n))
    (hfix : C.map xstar = xstar)
    (he : ∀ n, e n = ‖x n - xstar‖)
    (hduh : ∀ n, e (n + 1) ≤ C.q * e n) (n : ℕ) :
    ‖x n - xstar‖ ≤ C.q ^ n * ‖x 0 - xstar‖ := by
  exact picard_duhamel_orbit_error_geometric C x xstar e hx0 hxstar horbit hfix he hduh n

end NSFormalization.Paper1
