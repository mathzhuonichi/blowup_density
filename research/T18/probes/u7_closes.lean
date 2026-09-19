import NSFormalization.Section3.T18.Support
import Contracts.V1.PacketImport

/-!
# T18 U7 Spec-form closure probe

The four fields below are the U7 fields of `PeriodicInsertionAPI`, with every
Spec object replaced by its canonical `InsertionData` projection.  The
assembly-shaped constructor uses a registered `PacketImportAPI`, so the new
explicit premise of canonical `velocityDifference_support` is discharged by
`P.velocity_support`; no support premise remains in the result.
-/

noncomputable section

namespace NSFormalization.Section3.T18.U7Probe

open Set Metric
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1
open NSFormalization.Section3.T10
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17
open NSFormalization.Section3.T18
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

/-- The assembly input bundle specialized to a registered packet.  In
particular, its raw velocity and carrier projections are definitionally
`P.velocity` and `P.carrier`, respectively. -/
def insertionDataOfPacket {ν : ℝ} (P : PacketImportAPI ν)
    (place : PlacementData P.velocity P.pressure P.force P.carrier)
    (scaling : ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    InsertionData :=
  { ν := ν
    packetVelocity := P.velocity
    packetPressure := P.pressure
    packetForce := P.force
    carrier := P.carrier
    energyBound := P.energyBound
    dissipationBound := P.dissipationBound
    place := place
    scaling := scaling
    a := a
    g := g
    r := r
    δ := δ
    D := D
    reference := reference
    correction := correction
    hδ := hδ
    hg := hg
    ha := ha }

/-- Exactly the four U7 Spec fields under the canonical U1 projections. -/
structure PeriodicInsertionU7Fields (data : InsertionData) : Type where
  diffSupportRadius : ℝ
  diffSupportRadius_pos : 0 < diffSupportRadius
  velocityDifference_support :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data), ∀ t ∈ Ico (0 : ℝ) data.place.T,
      tsupport (fun x : NavierStokes.ProblemStatement.Space ↦ velocity data ε (t, x) -
        data.reference.velocity (t, x)) ⊆
          periodicSet (Metric.ball data.place.x₀ (ε * diffSupportRadius))
  diffSupport_in_chart :
    ∀ ε ∈ Ioc (0 : ℝ) (ε₀ data),
      Metric.ball data.place.x₀ (ε * diffSupportRadius) ⊆
        Metric.ball data.place.chartCenter data.place.chartRadius

/-- U12 assembly shape: all four U7 fields close, and the raw support premise
is supplied directly by the registered packet contract. -/
def insertionU7OfPacket {ν : ℝ} (P : PacketImportAPI ν)
    (place : PlacementData P.velocity P.pressure P.force P.carrier)
    (scaling : ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    let data := insertionDataOfPacket P place scaling a g r δ D reference
      correction hδ hg ha
    PeriodicInsertionU7Fields data := by
  let data := insertionDataOfPacket P place scaling a g r δ D reference
    correction hδ hg ha
  exact
    { diffSupportRadius := diffSupportRadius data
      diffSupportRadius_pos :=
        NSFormalization.Section3.T18.diffSupportRadius_pos data
      velocityDifference_support :=
        NSFormalization.Section3.T18.velocityDifference_support data
          P.velocity_support
      diffSupport_in_chart :=
        NSFormalization.Section3.T18.diffSupport_in_chart data }

end NSFormalization.Section3.T18.U7Probe
