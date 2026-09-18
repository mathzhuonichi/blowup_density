import NSFormalization.Section3.T20.CriticalRegularity

open scoped ENNReal

/- A concrete, nonempty choice of the five scalar constants and both
   bootstrap shrinkings.  This does not construct the API: it checks that the
   declared positive-threshold regime itself is not an empty interval. -/
example : ∃ (c C₀ C₁ CH1 Ccriterion : ℝ),
    0 < c ∧ 0 < C₀ ∧ 0 < C₁ ∧ 0 < CH1 ∧ 0 < Ccriterion ∧
      c < 1 / (4 * C₀) ∧ c < 1 / (4 * C₁) := by
  refine ⟨(1 : ℝ) / 8, 1, 1, 1, 1, ?_⟩
  norm_num
