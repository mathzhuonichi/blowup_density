import Bindings.CompactClassRider

/-!
Reviewer mutation probe for lane 254.

This is the complete main statement with the substantive force-error mutation
`f - g` -> `f + g`.  The final `exact` must fail: the proved theorem does not
establish smallness of the sum.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Section4
open scoped ENNReal

example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
        ∀ s : ℝ, s < criticalOrder q.toReal →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, g ∈ forceClassCompact →
              ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  ∀ τ : ℝ, 0 ≤ τ → τ < T →
                    ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                      ∃ f : SpaceTimeField, f ∈ forceClassCompact ∧
                        ∃ u : ClassicalSolutionR ν a f T,
                          maximalLifespanR ν a f = ENNReal.ofReal T ∧
                          forceSobolevENorm q s (f + g) < r ∧
                          energyENorm T (u.velocity - v.velocity) < η ∧
                          (∀ t : ℝ, 0 ≤ t → t ≤ τ →
                            ∀ x : NavierStokes.ProblemStatement.Space,
                            u.velocity (t, x) = v.velocity (t, x)) := by
  exact regularReference_compact

end BlowupDensity.Bindings
