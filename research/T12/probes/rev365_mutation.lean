import NSFormalization.Section3.T12.Cutoff

/- Negative review probe: changing the plateau value from `1` to `2` must
   invalidate the existing cube-equality proof.  This file is intentionally
   not expected to typecheck. -/

open Set
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section3.T12

example : ∀ x ∈ fundamentalCube, cutoff x = (2 : ℝ) := by
  intro x hx
  exact cutoff_eq_one x hx
