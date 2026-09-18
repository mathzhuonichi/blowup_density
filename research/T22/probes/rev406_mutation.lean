import NSFormalization.Section3.T22.CutoffMultiplierField
open NSFormalization.Section3.T22
open NavierStokes.ProblemStatement
open NSFormalization.Source.RealSobolev
open scoped ContDiff ENNReal
open NSFormalization.Paper3
-- Substantive mutation: halve the claimed multiplier constant in the conclusion.
example : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal (C / 2) * ‖A‖ₑ := by
  simpa using (cutoffMultiplier)
