import NSFormalization.Paper3.HomogeneousTime

/-! Minimal safe homogeneous realization contract.

This file records the proved compact-input realization boundary: homogeneous
Fourier data are controlled by physical L¹/L² quantities in the valid range.
A full `L² → 𝓢'` homogeneous multiplier is intentionally not introduced here.
-/
noncomputable section
namespace NSFormalization.Paper3
open NavierStokes.ProblemStatement
open scoped ContDiff

/-- Compact smooth inputs admit the finite homogeneous Fourier norm bound used
by the insertion estimates. This is a norm estimate, not the completed
tempered-distribution realization from the manuscript. -/
theorem compact_homogeneous_norm_bound {s C₁ C₂ : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) {f : Space → ℂ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (hC₁ : 0 ≤ C₁)
    (h₁ : (∫ x : Space, ‖f x‖) ≤ C₁)
    (h₂ : (∫ x : Space, ‖f x‖ ^ 2) ≤ C₂) :
    NSFormalization.Source.homogeneousFourierNorm s f ≤
      Real.sqrt (C₁ ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) + C₂) := by
  exact homogeneousFourierNorm_le_physical hs hs0 hf hc hC₁ h₁ h₂

end NSFormalization.Paper3
