import Contracts.V3.Continuation
import Bindings.ContinuationV3
import TestSupport.Axioms

noncomputable section

namespace BlowupDensity.Tests

open Set
open NavierStokes.ProblemStatement (Space)
open Contracts.V1.Data
open Contracts.V2.LocalTheory
open Contracts.V2.Continuation
open Contracts.V3.Continuation
open scoped ENNReal

/-- The implementation supplies both H¹-uniform continuation fields. -/
theorem checkedContinuationV3 : ContinuationV3API :=
  Bindings.continuationV3_holds

run_cmd TestSupport.checkAxioms ``checkedContinuationV3

/-- The restart duration precedes both the restart time and the smooth datum. -/
example :
    ∀ (ν : ℝ), 0 < ν →
      ∀ (f : SpaceTimeField), MemForceR f →
        ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
          ∃ δ : ℝ, 0 < δ ∧
            ∀ t₀ ∈ Icc (0 : ℝ) S,
              ∀ (a' : SpatialField), a' ∈ initialClassR →
                sobolevENorm 1 a' ≤ K →
                  ∃ w : ClassicalSolutionR ν a' (timeShift t₀ f) δ,
                    ManuscriptLocalRegularity ν a' (timeShift t₀ f) δ w :=
  checkedContinuationV3.restartH1

/-- A uniform H¹ bound yields a strict extension past the endpoint. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
            a ∈ initialClassR → SolvesBelow ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                sobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
                  ENNReal.ofReal (S + δ) < maximalLifespanR ν a f :=
  checkedContinuationV3.restartBeyondH1

end BlowupDensity.Tests
