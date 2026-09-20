import NSFormalization.Section4.I03.HomogeneousScaling
noncomputable section
open NavierStokes.ProblemStatement MeasureTheory NSFormalization.Source
open NSFormalization.Section4.I03
theorem rev250_wrong_exponent (s : ℝ) (f : Space → ℂ)
    {k : ℝ} (hk : 0 < k) :
    homogeneousFourierNorm s (concentratedForce k f) =
      k ^ (5 / 2 + s) * homogeneousFourierNorm s f := by
  unfold homogeneousFourierNorm
  rw [homogeneous_integral_concentrated s f hk, sqrt_rpow_energy hk]

