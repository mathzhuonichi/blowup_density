import Tests.ForceClasses

/-!
Reviewer negative probe: this deliberately widens the density range from
`s < criticalOrder q.toReal` to `s < criticalOrder q.toReal + 1`.
The registered proof must not inhabit this stronger, mathematically false shape.
-/

noncomputable section

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Tests
open scoped ENNReal

example :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          ∀ a : SpatialField, a ∈ initialClassR →
            s < criticalOrder q.toReal + 1 →
              RelativelyDense q s Y (breakdownSetIn Y ν a T) :=
  checkedForceClasses.density

end
