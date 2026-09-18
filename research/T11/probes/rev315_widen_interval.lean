import NSFormalization.Section3.T11.Uniqueness

/-!
Reviewer negative probe: this deliberately widens the common interval from
`Ico 0 (min T₁ T₂)` to `Ico 0 (max T₁ T₂)`.  The lane theorem must not prove it.
-/

noncomputable section

namespace NSFormalization.Section3.T11.Review315

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11

example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T₁ T₂ : ℝ) (u₁ : ClassicalSolutionT ν a f T₁)
          (u₂ : ClassicalSolutionT ν a f T₂),
          ∀ t ∈ Ico (0 : ℝ) (max T₁ T₂), ∀ x : Space,
            u₁.velocity (t, x) = u₂.velocity (t, x) := by
  exact velocity_unique

end NSFormalization.Section3.T11.Review315
