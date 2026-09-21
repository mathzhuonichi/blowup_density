import Contracts.V2.TorusLocalTheory
import Bindings.TorusLocalTheoryV2
import TestSupport.Axioms

noncomputable section

namespace BlowupDensity.Tests

open Set
open NavierStokes.ProblemStatement (Space)
open Contracts.V1.Data
open Contracts.V1.TorusData
open Contracts.V1.TorusLocalTheory
open Contracts.V2.TorusLocalTheory
open scoped ENNReal

/-- The implementation retains V1 and supplies both H¹-uniform V2 fields. -/
theorem checkedTorusLocalTheoryV2 : torusLocalTheoryV2Statement :=
  Bindings.torusLocalTheoryV2_holds

run_cmd TestSupport.checkAxioms ``checkedTorusLocalTheoryV2

/-- The restart duration precedes the restart time and smooth datum. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w :=
  checkedTorusLocalTheoryV2.2.restart

/-- A uniform H¹ trajectory bound yields a larger periodic classical solution
with exact velocity and normalized-pressure overlap. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ (a : SpatialField), a ∈ initialClassT →
            ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
              SolvesBelowT ν a f S u p →
                (∀ t ∈ Ico (0 : ℝ) S,
                  periodicSobolevENorm 1 (fun x : Space => u (t, x)) ≤ K) →
                    ∃ v : ClassicalSolutionT ν a f (S + δ),
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.velocity (t, x) = u (t, x)) ∧
                      (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                        v.pressure (t, x) = p (t, x)) :=
  checkedTorusLocalTheoryV2.2.restartBeyond

end BlowupDensity.Tests
