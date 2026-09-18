import Contracts.V1.TorusLocalTheory
import Bindings.TorusLocalTheory
import TestSupport.Axioms

/-! Public-type, `Spec`-field conformance, and transitive-axiom checks for
`T01.torus_local_theory` V1.

The registered continuation component is the `H³` narrowing
`PeriodicContinuationH3API`.  The manuscript's two `H¹` sentences are the named
predicates `PeriodicRestartH1` / `PeriodicRestartBeyondH1`; the last example
below records that the manuscript package follows from exactly those two and is
**not** claimed by this test. -/

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

/-- The exact residue: the manuscript's `PeriodicContinuationAPI` follows from
the two named `H¹` predicates together with the three registered ball-free
fields, and from nothing weaker.  Both predicates remain hypotheses here; the
test claims neither. -/
example (h₁ : PeriodicRestartH1) (h₂ : PeriodicRestartBeyondH1) :
    PeriodicContinuationAPI :=
  Bindings.TorusLocalTheory.torusContinuationAPI_of_h1 h₁ h₂

end BlowupDensity.Tests
