import Tests.LocalTheoryV2

open BlowupDensity.Contracts.V1.Data BlowupDensity.Tests
open scoped ENNReal

-- Control: every quantifier and hypothesis of the registered H7 field.
example :
    ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ initialClassR → sobolevENorm 7 a ≤ K →
        δ ≤ checkedLocalTheoryV2.horizon ν a f :=
  checkedLocalTheoryV2.horizon_lower_bound

-- Substantive mutation: widen the datum class from an H7 ball to an H1 ball.
-- All binders and membership/finiteness/positivity hypotheses are retained.
example :
    ∀ ν, 0 < ν → ∀ f, MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ initialClassR → sobolevENorm 1 a ≤ K →
        δ ≤ checkedLocalTheoryV2.horizon ν a f :=
  checkedLocalTheoryV2.horizon_lower_bound
