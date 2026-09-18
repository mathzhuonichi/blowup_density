import NSFormalization.Section3.T13.ConstantEndpoints

noncomputable section

namespace NSFormalization.Section3.T13

/-! Negative review probe: flip the substantive positivity conclusion in
`constant_pos_finite` to a negative one.  The shipped theorem must no longer
typecheck against this mutated statement. -/
example (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    cFrac s < 0 ∧ cFrac s < ⊤ := by
  exact constant_pos_finite s hs0 hs1

end NSFormalization.Section3.T13
