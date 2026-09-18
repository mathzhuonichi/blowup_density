import NSFormalization.Section3.T22.CutoffMultiplier
import NSFormalization.Section3.T22.Domain

noncomputable section

namespace NSFormalization.Section3.T22

open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal

-- The lane brief requires this exact theorem; the implementation does not define it.
example : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ := by
  exact NSFormalization.Section3.T22.cutoffMultiplier

end NSFormalization.Section3.T22
