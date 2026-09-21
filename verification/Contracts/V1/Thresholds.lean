import Mathlib.Data.Real.Basic

/-! Stable specification for the Section 4 threshold-arithmetic component.
This does not assert a PDE estimate, existence theorem, or density theorem.
Version 1 is independent of implementation modules and declaration names. -/

namespace BlowupDensity.Contracts.V1

/-- A concrete force exponent and its exact arithmetic obligations. -/
structure ThresholdAPI where
  exponent : ℝ → ℝ → ℝ
  formula : ∀ q s : ℝ, exponent q s = 2 / q - 3 / 2 - s
  positive : ∀ q s : ℝ, 0 < exponent q s ↔ s < 2 / q - 3 / 2
  l1 : ∀ s : ℝ, exponent 1 s = 1 / 2 - s
  l2 : ∀ s : ℝ, exponent 2 s = -1 / 2 - s
  negativeIndex : ∀ s : ℝ, s < -1 / 2 →
    ∃ r : ℝ, -3 / 2 < r ∧ r < -1 / 2 ∧ s < r
  energy : exponent 1 0 = 1 / 2 ∧ exponent 2 (-1) = 1 / 2

end BlowupDensity.Contracts.V1
