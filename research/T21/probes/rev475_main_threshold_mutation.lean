import NSFormalization.Section3.T21.MainAssembly

/-!
Reviewer negative probe: mutate the zero-datum threshold in `thm:main` from
`1 / 2` to `2 / 3`.  The canonical proof must not inhabit this statement.
-/

noncomputable section

namespace NSFormalization.Section3.T21.ReviewerMutation

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10

example : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 2 / 3 :=
  closedMainTheoremAPI.zeroInitialDensityIff

end NSFormalization.Section3.T21.ReviewerMutation
