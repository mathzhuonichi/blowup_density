import NSFormalization.Section3.T19.Assembly

/-!
# Reviewer mutation probe for lane 470

This deliberately widens the headline density range from `s < 1 / 2` to
`s < 3 / 2`.  The canonical theorem must not prove this mutated statement.
-/

noncomputable section

namespace NSFormalization.Section3.T19.ReviewerMutation

open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 3 / 2 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T) :=
  periodicDensityStatement_holds

end NSFormalization.Section3.T19.ReviewerMutation
