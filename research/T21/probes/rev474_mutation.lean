import NSFormalization.Section3.T21.Main

noncomputable section

namespace NSFormalization.Section3.T21.Rev474Mutation

open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19 (periodicDensityAPI)
open NSFormalization.Section3.T21
open NSFormalization.Section4.A02 (SpatialField)

/-- Deliberately false proof attempt: widen the main density interval from
`s < 1 / 2` to `s < 3 / 4` while reusing the delivered proof. -/
example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ nu : ℝ, 0 < nu → ∀ T : ℝ, 0 < T →
        ∀ s : ℝ, s < 3 / 4 →
          RelativelyDenseT 1 s forceClassT (breakdownSetT nu a T) := by
  exact fixedInitialDensity periodicDensityAPI

end NSFormalization.Section3.T21.Rev474Mutation
