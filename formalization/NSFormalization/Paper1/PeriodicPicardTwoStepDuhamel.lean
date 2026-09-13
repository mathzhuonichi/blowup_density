import NSFormalization.Paper1.PeriodicPicardTwoStepOrbit

noncomputable section
namespace NSFormalization.Paper1

/-- Conditional composition of a Duhamel gain sequence with an explicit Picard
orbit: the two scalar inequalities produce geometric orbit control. -/
theorem picard_two_step_duhamel_orbit_bound
    {E : Type*} [NormedAddCommGroup E]
    (C : PicardContractionContract E) (x : ℕ → E) (xstar : E)
    (e d : ℕ → ℝ) {t : ℝ}
    (hx0 : x 0 ∈ C.ball) (hxstar : xstar ∈ C.ball)
    (horbit : ∀ n, x (n + 1) = C.map (x n))
    (hfix : C.map xstar = xstar)
    (he : ∀ n, e n = ‖x n - xstar‖)
    (hgain : ∀ n, e (n + 1) ≤ t * d n)
    (hcompare : ∀ n, t * d n ≤ C.q * e n) (n : ℕ) :
    ‖x n - xstar‖ ≤ C.q ^ n * ‖x 0 - xstar‖ := by
  apply picard_two_step_orbit_error_bound C x xstar e hx0 hxstar horbit hfix he
  intro m
  exact (hgain m).trans (hcompare m)

end NSFormalization.Paper1
