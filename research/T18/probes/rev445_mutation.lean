import NSFormalization.Section3.T18.SobolevRate

/-! Reviewer-only negative probe for lane 445.  This file is intentionally
expected not to elaborate: it removes the factor `2` that absorbs both
lower-order terms in `eq:Hsclose`. -/

noncomputable section
namespace NSFormalization.Section3.T18.Rev445

open Set
open NSFormalization.Section3.T10
open scoped ENNReal

/-- Substantive mutation: halve the main rate constant. -/
def smallerForceDiffSobolevConst (data : InsertionData) (s : ℝ) : ℝ :=
  data.scaling.sobolevConst s + data.correction.sobolevConst s

theorem smaller_constant_mutation (data : InsertionData) :
    ∀ s : ℝ, 0 ≤ s → s < 1 / 2 → ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      forceSobolevENormT 1 s (fun z ↦ force data ε z - data.g z) ≤
        ENNReal.ofReal (smallerForceDiffSobolevConst data s *
          (ε ^ ((1 : ℝ) / 2 - s) + ε ^ ((3 : ℝ) / 2 - s))) := by
  intro s hs hsHalf ε hε
  exact forceDifference_sobolev_bound data s hs hsHalf ε hε

end NSFormalization.Section3.T18.Rev445
