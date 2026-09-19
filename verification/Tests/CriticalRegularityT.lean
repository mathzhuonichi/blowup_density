import Contracts.V1.CriticalRegularityT
import Bindings.CriticalRegularityT
import TestSupport.Axioms

/-! Public-type, Spec-field conformance, axiom, and non-vacuity checks for
`T03.critical_regularity` V1. -/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open NavierStokes.ProblemStatement
open Contracts.V1.Data
open Contracts.V1.TorusData
open Contracts.V1.TorusLocalTheory
open Contracts.V1.MeanZeroCalculus
open Contracts.V1.CriticalRegularityT
open scoped ContDiff ENNReal BigOperators

/-- The implementation supplies the complete 23-field T20 package. -/
noncomputable def checkedCriticalRegularityT : CriticalRegularityTAPI :=
  Bindings.criticalRegularityT

run_cmd TestSupport.checkAxioms ``checkedCriticalRegularityT

/-- Conformance with `research/T20/Spec.lean` field `meanBound`. -/
example : ∀ (g : SpaceTimeField), g ∈ forceClassT →
    ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal ‖meanPathT g t‖ ≤ meanForceIntegralT g t ∧
        meanForceIntegralT g t ≤ criticalRho g :=
  checkedCriticalRegularityT.meanBound

/-- Conformance with `research/T20/Spec.lean` field
`constantTransportCommutesLambda`. -/
example : ∀ (m : Space) (v Lv : SpatialField), SmoothPeriodicT v →
    IsPeriodicLambda v Lv →
      IsPeriodicLambda (constantTransportSpatialT m v)
        (constantTransportSpatialT m Lv) :=
  checkedCriticalRegularityT.constantTransportCommutesLambda

/-- Conformance with `research/T20/Spec.lean` field `globalRegularity`. -/
example : ∀ (ν : ℝ), 0 < ν →
    ∀ (g : SpaceTimeField), g ∈ forceClassT →
      criticalRho g < ENNReal.ofReal (checkedCriticalRegularityT.c * ν) →
        maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ :=
  checkedCriticalRegularityT.globalRegularity

/-- The proposition form is inhabited by the registered record. -/
example : criticalRegularityStatement :=
  ⟨checkedCriticalRegularityT⟩

/-- Non-vacuity at a genuinely nonzero compactly time-supported force. -/
example : ∃ (ν : ℝ) (g : SpaceTimeField) (_hg : g ∈ forceClassT),
    0 < ν ∧ g (2, 0) ≠ 0 ∧
      criticalRho g < ENNReal.ofReal (checkedCriticalRegularityT.c * ν) ∧
      maximalLifespanT ν (fun _ : Space ↦ 0) g = ⊤ :=
  Bindings.CriticalRegularityT.criticalRegularity_nonvacuous

end BlowupDensity.Tests
