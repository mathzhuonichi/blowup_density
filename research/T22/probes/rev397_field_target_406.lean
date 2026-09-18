import NSFormalization.Section3.T22.CutoffMultiplierField

/-!
The reviewer's REJECT criterion for lane 397
(`research/T22/probes/rev397_field_target.lean`, which imports only
`CutoffMultiplier` and `Domain`) is now met by lane 406: the same `example`
closes verbatim once `Section3/T22/CutoffMultiplierField` is imported.
The original probe is left untouched as the record of the 397 review.
-/

noncomputable section

namespace NSFormalization.Section3.T22

open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff ENNReal

example : ∀ (s : ℝ) (χ : Space → ℝ),
    ContDiff ℝ ∞ χ → HasCompactSupport χ →
    ∃ C : ℝ, 0 < C ∧ ∀ A : RealVectorSobolev s,
      ∃ B : RealVectorSobolev s,
        IsCutoffDatum s χ A B ∧ ‖B‖ₑ ≤ ENNReal.ofReal C * ‖A‖ₑ := by
  exact NSFormalization.Section3.T22.cutoffMultiplier

end NSFormalization.Section3.T22
