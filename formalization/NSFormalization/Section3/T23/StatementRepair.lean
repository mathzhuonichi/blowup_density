import NSFormalization.Section3.T23.LocalCorrection

/-! G0's raw-field obstruction. The exact reconciled API and its repaired
quantifiers are checked in research/T23/probes/g0_counterexample.lean.
The implementation layer does not import contract records. -/
noncomputable section
namespace NSFormalization.Section3.T23

/-- Raw cutoff data permit zero threshold; there are no positivity fields. -/
def zeroCutoff : CutoffData :=
  ⟨fun _ => 0, fun _ => 0, ∅, 0, 0, fun _ => 0, fun _ _ => 0⟩

/-- The two threshold clauses of the insertion API cannot both hold at this
actual cutoff. The research probe applies the contradiction to the literal API. -/
theorem zeroCutoff_no_positive_threshold :
    ¬ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ zeroCutoff.ε₀ := by
  rintro ⟨ε₀, hp, hl⟩
  exact (not_lt_of_ge hl) hp

end NSFormalization.Section3.T23
