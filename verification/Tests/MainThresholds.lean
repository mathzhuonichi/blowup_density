import Contracts.V1.MainThresholds
import Bindings.MainThresholds
import TestSupport.Axioms

/-! Four literal Spec-field conformance checks and a transitive axiom audit. -/
noncomputable section
namespace BlowupDensity.Tests
open Filter Set
open Contracts.V1.Data
open scoped ENNReal Topology

theorem checkedMainThresholds : Contracts.V1.MainThresholds.MainThresholdsAPI :=
  Bindings.mainThresholds

run_cmd TestSupport.checkAxioms ``checkedMainThresholds

/-- Conformance with Spec.lean `fixedInitialDensity`. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        ∀ a : SpatialField, a ∈ initialClassR →
          s < criticalOrder q.toReal → BreakdownDenseR ν a T q s :=
  checkedMainThresholds.fixedInitialDensity

/-- Conformance with Spec.lean `zeroInitialDensityIff`. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        RelativelyDense q s forceClassR (breakdownSetRZero ν T) ↔
          s < criticalOrder q.toReal :=
  checkedMainThresholds.zeroInitialDensityIff

/-- Conformance with Spec.lean `thresholdValues`. -/
example :
    criticalOrder 1 = (1 : ℝ) / 2 ∧ criticalOrder 2 = -(1 : ℝ) / 2 :=
  checkedMainThresholds.thresholdValues

/-- Conformance with Spec.lean `regularReferenceApproximation`. -/
example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ q : ℝ≥0∞, (q = 1 ∨ q = 2) → ∀ s : ℝ,
        s < criticalOrder q.toReal →
          ∀ a : SpatialField, a ∈ initialClassR →
            ∀ g : SpaceTimeField, MemForceR g →
              ∀ δ : ℝ, 0 < δ → ∀ v : ClassicalSolutionR ν a g (T + δ),
                ∃ ε₀ : ℝ, 0 < ε₀ ∧
                  ∃ f u : ℝ → SpaceTimeField,
                    (∀ ε ∈ Ioo 0 ε₀,
                      MemForceR (f ε) ∧
                      maximalLifespanR ν a (f ε) = ENNReal.ofReal T ∧
                      ∃ U : ClassicalSolutionR ν a (f ε) T,
                        U.velocity = u ε ∧
                        ∀ t ∈ Icc 0 (T - 2 * ε ^ 2), ∀ x,
                          u ε (t, x) = v.velocity (t, x)) ∧
                    Tendsto (fun ε => forceSobolevENorm q s (f ε - g))
                      (𝓝[>] 0) (𝓝 0) ∧
                    Tendsto (fun ε => energyENorm T (u ε - v.velocity))
                      (𝓝[>] 0) (𝓝 0) :=
  checkedMainThresholds.regularReferenceApproximation

end BlowupDensity.Tests
