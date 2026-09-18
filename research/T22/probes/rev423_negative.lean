import NSFormalization.Section3.T22.Assembly

/-! Reviewer-only negative probe: halve the cutoff multiplier constant in the
    assembled API field.  The original field theorem must not close this
    substantively changed conclusion. -/

noncomputable section

namespace NSFormalization.Section3.T22.Rev423

open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open scoped ContDiff ENNReal

example : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧
          ‖B‖ₑ ≤ ENNReal.ofReal (C / 2) * ‖A‖ₑ := by
  simpa using boundedDomainNorm.cutoffMultiplier

end NSFormalization.Section3.T22.Rev423
