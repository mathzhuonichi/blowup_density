import NSFormalization.Section3.T24.MultipleRegions

/-!
Reviewer negative probe for lane 469. The main dissipation identity's constant is
substantively changed from `E ^ 2` to `E ^ 2 + 1`, with all binders retained.
Replaying the shipped theorem must fail by a type mismatch.
-/
noncomputable section

namespace Rev469WrongDissipationConstant

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T24
open scoped ENNReal

variable {nu : ℝ} {u f : VelocityField} {p : PressureField}
  {K : Set Space} {M E : ℝ} (d : RegionsData nu u p f K M E)

example : (energyGradientT d.T d.assembledVelocity) ^ (2 : ℕ) =
    ENNReal.ofReal ((E ^ 2 + 1) * ∑ j, d.ε j) := by
  exact d.dissipation_bound

end Rev469WrongDissipationConstant
