import Contracts.V1.ForceClasses
import Bindings.CompactClassRider
import Bindings.RapidClassDensity

/-!
# Binding for Corollary 4.5

The guarded density and zero-data fields and the Schwartz specialization are
supplied by lane 257. The regular-reference field is the remaining guarded
case split between lanes 254 and 257.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Contracts.V1 Contracts.V1.Data
open scoped ENNReal

/-- The complete guarded `ForceClassesAPI.regularReference` field, assembled
from the compact and rapid instances. -/
theorem regularReference :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) →
          ∀ s : ℝ, s < criticalOrder q.toReal →
            ∀ a : SpatialField, a ∈ initialClassR →
              ∀ g : SpaceTimeField, g ∈ Y → ∀ δ : ℝ, 0 < δ →
                ∀ v : ClassicalSolutionR ν a g (T + δ),
                  ∀ τ : ℝ, 0 ≤ τ → τ < T →
                    ∀ r η : ℝ≥0∞, 0 < r → 0 < η →
                      ∃ f : SpaceTimeField, f ∈ Y ∧
                        ∃ u : ClassicalSolutionR ν a f T,
                          maximalLifespanR ν a f = ENNReal.ofReal T ∧
                          forceSobolevENorm q s (f - g) < r ∧
                          energyENorm T (u.velocity - v.velocity) < η ∧
                          (∀ t : ℝ, 0 ≤ t → t ≤ τ →
                            ∀ x : NavierStokes.ProblemStatement.Space,
                            u.velocity (t, x) = v.velocity (t, x)) := by
  intro Y hY
  rcases hY with rfl | rfl
  · exact regularReference_compact
  · exact regularReference_rapid

/-- Complete, statement-faithful witness of the reconciled four-field API. -/
theorem forceClasses : ForceClasses.ForceClassesAPI where
  density := density
  zeroIff := zeroIff
  schwartzDensity := schwartzDensity
  regularReference := regularReference

end BlowupDensity.Bindings
