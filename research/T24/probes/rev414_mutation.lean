import NSFormalization.Section3.T24.AffineForce
open Set
open NSFormalization.Section3.T24
open NavierStokes.ProblemStatement
open scoped ContDiff
example {ν : ℝ} {U F : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₀ : 0 < τ₀) (hτ₁ : τ₁ < 2)
    (hvelocity_smooth : ContDiffOn ℝ ∞ U preSingularDomain)
    (hforce_smooth : ContDiff ℝ ∞ F) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      ContDiff ℝ ∞ (affineForce ν U F b) := by
  intro b hb
  exact force_smooth c r τ₀ τ₁ hτ₀ (by linarith) hvelocity_smooth hforce_smooth b hb
