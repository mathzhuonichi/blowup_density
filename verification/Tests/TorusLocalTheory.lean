import Contracts.V1.TorusLocalTheory
import Bindings.TorusLocalTheory
import TestSupport.Axioms

/-! Typed and transitive-axiom checks for the current periodic local-theory, H3 continuation, mean-reduction and viscosity-rescaling interfaces. -/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open NavierStokes.ProblemStatement
open Contracts.V1.Data
open Contracts.V1.TorusData
open Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal

/-- The implementation supplies all four periodic local-theory APIs: the
eight-field local theory, the `H³`-narrowed five-field continuation package,
the six-field Galilean mean reduction, and the four-field viscosity
rescaling. -/
noncomputable def checkedTorusLocalTheory :
    Contracts.V1.TorusLocalTheory.TorusLocalTheoryAPI :=
  Bindings.torusLocalTheory

run_cmd TestSupport.checkAxioms ``checkedTorusLocalTheory

/-- Conformance with `research/T11/Spec.lean` field
`PeriodicLocalTheoryAPI.regularity`: the selected solution on the selected
horizon carries all three regularity clauses. -/
example : ∀ (ν : ℝ) (hν : 0 < ν)
    (a : SpatialField) (ha : a ∈ initialClassT)
    (f : SpaceTimeField) (hf : f ∈ forceClassT),
      PeriodicLocalRegularity ν a f
        (checkedTorusLocalTheory.localTheory.horizon ν a f)
        (checkedTorusLocalTheory.localTheory.solution ν hν a ha f hf) :=
  checkedTorusLocalTheory.localTheory.regularity

/-- Conformance with `research/T11/Spec.lean` field
`PeriodicLocalTheoryAPI.exists_maximal`. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∃ (u : SpaceTimeField) (p : SpaceTimeScalar),
          IsMaximalPeriodicSolution ν a f u p :=
  checkedTorusLocalTheory.localTheory.exists_maximal

/-- Conformance with `research/T11/Spec.lean` field
`PeriodicContinuationAPI.extendsBeyond`, which carries no datum ball and is
therefore registered verbatim. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (S : ℝ), 0 < S →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p → squaredHTwoIntegralT S u ≠ ⊤ →
              ExtendsBeyondT ν a f S u p :=
  checkedTorusLocalTheory.continuation.extendsBeyond

/-- Conformance with `research/T11/Spec.lean` field
`PeriodicContinuationAPI.restart` **after the registered narrowing**: the datum
ball is `H³`, everything else is the manuscript's wording. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 3 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w :=
  checkedTorusLocalTheory.continuation.restart

/-- Conformance with `research/T11/Spec.lean` field
`PeriodicMeanReductionAPI.mean_formula`. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∀ t ∈ Ico (0 : ℝ) T,
            velocityMeanT w.velocity t = galileanMeanT a f t :=
  checkedTorusLocalTheory.meanReduction.mean_formula

/-- Conformance with `research/T11/Spec.lean` field
`PeriodicViscosityRescalingAPI.to_unit`. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        ∀ (T : ℝ) (w : ClassicalSolutionT ν a f T),
          ∃ v : ClassicalSolutionT 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T),
            v.velocity = unitViscosityVelocityT ν w.velocity ∧
            v.pressure = unitViscosityPressureT ν w.pressure ∧
            PeriodicLocalRegularity 1 (unitViscosityInitialT ν a)
              (unitViscosityForceT ν f) (ν * T) v :=
  checkedTorusLocalTheory.viscosityRescaling.to_unit

end BlowupDensity.Tests
