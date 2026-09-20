import Contracts.V1.Density
import Bindings.Density
import TestSupport.Axioms

/-! Public statement and axiom checks for `T03.density` V1. -/

noncomputable section

namespace BlowupDensity.Tests

open Set Filter Topology
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.Density
open scoped ENNReal Topology

/-- Checked `prop:density` (`03-torus.tex:349-368`). -/
theorem checkedPeriodicDensity : periodicDensityStatement :=
  Bindings.Density.periodicDensityStatement_holds

run_cmd TestSupport.checkAxioms ``checkedPeriodicDensity

/-- Checked `cor:mixed` (`03-torus.tex:528-538`). -/
theorem checkedMixedRegion : mixedRegionStatement :=
  Bindings.Density.mixedRegionStatement_holds

run_cmd TestSupport.checkAxioms ``checkedMixedRegion

/-- Checked `cor:closure` (`03-torus.tex:540-561`). -/
theorem checkedStrongClosure : strongClosureStatement :=
  Bindings.Density.strongClosureStatement_holds

run_cmd TestSupport.checkAxioms ``checkedStrongClosure

/-- Checked `prop:projection` (`03-torus.tex:564-590`). -/
theorem checkedProjection : projectionStatement :=
  Bindings.Density.projectionStatement_holds

run_cmd TestSupport.checkAxioms ``checkedProjection

/-- The single registry declaration bundles all four paper statements. -/
theorem checkedDensity :
    periodicDensityStatement ∧ mixedRegionStatement ∧
      strongClosureStatement ∧ projectionStatement :=
  ⟨checkedPeriodicDensity, checkedMixedRegion,
    checkedStrongClosure, checkedProjection⟩

run_cmd TestSupport.checkAxioms ``checkedDensity

/-! Independent field-shape checks for the non-headline clauses. -/

example : criticalOrder 1 = (1 : ℝ) / 2 :=
  Bindings.Density.periodicDensityAPI.thresholdValue

example :
    0 < BlowupDensity.Contracts.V1.alpha 2 1 ∧
      0 < BlowupDensity.Contracts.V1.alpha (4 / 3) 2 :=
  Bindings.Density.mixedRegionAPI.regionExamples

example :
    ∀ a : SpatialField, a ∈ initialClassT →
      ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
        ∀ g : SpaceTimeField, g ∈ forceClassT →
          ∀ δ : ℝ, 0 < δ →
            ∀ reference : ClassicalSolutionT ν a g (T + δ),
              energyENormT T reference.velocity < ⊤ :=
  Bindings.Density.strongClosureAPI.referenceFiniteEnergy

example :
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      Prod.fst ''
          {p : SpatialField × SpaceTimeField |
            p ∈ extendedBreakdownSetT ν T ∧ p.1 = (fun _ => 0)} =
        {(fun _ => 0 : SpatialField)} :=
  Bindings.Density.projectionAPI.zeroInitialProjection

end BlowupDensity.Tests
