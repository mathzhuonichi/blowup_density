import Contracts.V1.ForceClasses
import Bindings.ForceClasses
import TestSupport.Axioms

/-! Four literal Spec-field conformance checks and a transitive axiom audit. -/
noncomputable section

namespace BlowupDensity.Tests

open Contracts.V1.Data
open scoped ENNReal

theorem checkedForceClasses : Contracts.V1.ForceClasses.ForceClassesAPI :=
  Bindings.forceClasses

run_cmd TestSupport.checkAxioms ``checkedForceClasses

/-- Conformance with `research/R45/Spec.lean` field `density`. -/
example :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          ∀ a : SpatialField, a ∈ initialClassR →
            s < criticalOrder q.toReal →
              RelativelyDense q s Y (breakdownSetIn Y ν a T) :=
  checkedForceClasses.density

/-- Conformance with `research/R45/Spec.lean` field `zeroIff`. -/
example :
    ∀ Y : Set SpaceTimeField, (Y = forceClassCompact ∨ Y = forceClassRapid) →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
          RelativelyDense q s Y
              (breakdownSetIn Y ν (fun _ => 0) T) ↔
            s < criticalOrder q.toReal :=
  checkedForceClasses.zeroIff

/-- Conformance with `research/R45/Spec.lean` field `schwartzDensity`. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassSchwartz →
          s < criticalOrder q.toReal →
            RelativelyDense q s forceClassRapid
              (breakdownSetIn forceClassRapid ν a T) :=
  checkedForceClasses.schwartzDensity

/-- Conformance with `research/R45/Spec.lean` field `regularReference`. -/
example :
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
                            u.velocity (t, x) = v.velocity (t, x)) :=
  checkedForceClasses.regularReference

end BlowupDensity.Tests
