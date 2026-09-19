import NSFormalization.Section3.T19.DensityEngine

namespace NSFormalization.Section3.T19

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section3.T10

-- Deliberate mutation: widen the proved range from `s < 1 / 2` to `s < 3 / 4`.
example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 3 / 4 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T) := by
  exact fixedInitialDensity

end NSFormalization.Section3.T19
