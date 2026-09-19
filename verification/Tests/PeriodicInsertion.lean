import Contracts.V1.PeriodicInsertion
import Bindings.PeriodicInsertion
import TestSupport.Axioms

noncomputable section
namespace BlowupDensity.Tests
open Set MeasureTheory Filter Topology
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal

/-- Every one of the 45 fields, with precisely the Spec's threaded parameters. -/
theorem checkedPeriodicInsertion : BlowupDensity.T18.Spec.periodicInsertionStatement :=
  Bindings.PeriodicInsertion.periodicInsertionStatement_holds

run_cmd TestSupport.checkAxioms ``checkedPeriodicInsertion

section Conformance
variable {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)

local notation "A" => Bindings.PeriodicInsertion.periodicInsertion P place scaling a g r δ D reference correction hδ hg ha

-- Spec conformance: momentum.
example : ∀ ε ∈ Ioc (0 : ℝ) (A).ε₀,
    ∀ t ∈ Ioo (0 : ℝ) place.T, ∀ x : Space,
      navierStokesResidual ν ((A).velocity ε) ((A).pressure ε) t x = (A).force ε (t, x) := (A).momentum

-- Spec conformance: velocityDifference_support.
example : ∀ ε ∈ Ioc (0 : ℝ) (A).ε₀,
    ∀ t ∈ Ico (0 : ℝ) place.T,
      tsupport (fun x : Space => (A).velocity ε (t, x) - reference.velocity (t, x)) ⊆
        Contracts.V1.periodicSet (Metric.ball place.x₀ (ε * (A).diffSupportRadius)) := (A).velocityDifference_support

-- Spec conformance: energyRate.
example : ∀ ε ∈ Ioc (0 : ℝ) (A).ε₀,
    energyENormT place.T (fun z => (A).velocity ε z - reference.velocity z) ≤
      ENNReal.ofReal ((P.energyBound + P.dissipationBound) * ε ^ ((1 : ℝ) / 2) +
        correction.energyConst * ε ^ ((3 : ℝ) / 2)) := (A).energyRate

end Conformance

/-- This is conditional: T15 U15 and T17 U12 must supply the displayed
witnesses; the already registered T13 and T11 results add no new gate. -/
example {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)
    (hw : ∃ _scaling : BlowupDensity.T15.Draft.ScalingAPI P place,
      ∃ reference : ClassicalSolutionT ν a g (place.T + δ),
        Nonempty (BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)) :
    Nonempty (Σ scaling : BlowupDensity.T15.Draft.ScalingAPI P place,
      Σ reference : ClassicalSolutionT ν a g (place.T + δ),
      Σ correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D,
        BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction) :=
  Bindings.PeriodicInsertion.nonvacuity_of_witnesses P place a g r δ D hδ hg ha hw

end BlowupDensity.Tests
