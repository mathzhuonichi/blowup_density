import Bindings.CompactClassDensity

open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings
open scoped ENNReal

/-!
Reviewer mutation probe: widening the strict subcritical range to include the
critical endpoint must not be derivable from `density_compact`.
-/
example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassR →
          s ≤ criticalOrder q.toReal →
            RelativelyDense q s forceClassCompact
              (breakdownSetIn forceClassCompact ν a T) := by
  intro ν hν T hT q hq s a ha hs
  exact density_compact ν hν T hT q hq s a ha hs
