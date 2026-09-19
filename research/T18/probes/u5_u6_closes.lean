import NSFormalization.Section3.T18.Momentum
import Bindings.TorusLocalTheory
import Contracts.V1.PacketImport

/-! T18 U5/U6 Spec-form conformance. The U1 adapters below are copied
verbatim from u2_u4_closes.lean so this research probe is standalone. -/

noncomputable section

namespace BlowupDensity.T18.U5U6ClosesProbe

open Set
open scoped ContDiff
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusData
open NSFormalization.Section3.T15
open NSFormalization.Section3.T16
open NSFormalization.Section3.T17

namespace Spec

/-- The T15 Spec placement record, restated in packet-projection form for this
probe.  All seventeen fields are converted below. -/
structure PlacementData {nu : ℝ} (P : PacketAPI nu) where
  T : ℝ
  time_pos : 0 < T
  chartCenter : Space
  chartRadius : ℝ
  chartRadius_pos : 0 < chartRadius
  chartBall_in_cube :
    closure (Metric.ball chartCenter chartRadius) ⊆
      interior NSFormalization.Section3.T13.fundamentalCube
  x₀ : Space
  x₀_mem : x₀ ∈ Metric.ball chartCenter chartRadius
  Kstar : Set Space
  Kstar_compact : IsCompact Kstar
  carrier_subset : P.carrier ⊆ Kstar
  force_projection_subset : ∀ t : ℝ, ∀ x : Space,
    (t, x) ∈ tsupport P.force → x ∈ Kstar
  ε₀ : ℝ
  eps_pos : 0 < ε₀
  eps_le_one : ε₀ ≤ 1
  eps_time : ∀ ε ∈ Ioc (0 : ℝ) ε₀, 2 * ε ^ 2 < T
  eps_space : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ y ∈ Kstar,
    x₀ + ε • y ∈ Metric.ball chartCenter chartRadius

/-- The T16 Spec cutoff data.  Positivity of its threshold is intentionally
not a raw field; it comes from the converted `LocalPotentialAPI` carried by
the correction record. -/
structure CutoffData where
  θ : Space → ℝ
  η : ℝ → ℝ
  plateau : Set Space
  θRadius : ℝ
  ε₀ : ℝ
  potential : SpaceTimeField
  correction : ℝ → SpaceTimeField

/-- Fieldwise cutoff conversion used by the Spec-spelled force below. -/
def CutoffData.toCanonical (D : CutoffData) :
    NSFormalization.Section3.T16.CutoffData :=
  { θ := D.θ
    η := D.η
    plateau := D.plateau
    θRadius := D.θRadius
    ε₀ := D.ε₀
    potential := D.potential
    correction := D.correction }

/-- The reconciled Spec's correction-force spelling after the fieldwise T16
data conversion.  Lane 394 proves this is `rfl`-equal to the copied T17 Spec
definition. -/
def correctionForce (nu : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    SpaceTimeField :=
  NSFormalization.Section3.T17.correctionForce nu v D.toCanonical ε

/-- The reconciled Spec's packet-argument spelling of the periodized velocity.
Lane 384 proves this definition is `rfl`-equal to the copied T15 Spec
definition. -/
def periodizedScaledVelocity {nu : ℝ} (P : PacketImportAPI nu) (x₀ : Space)
    (T ε : ℝ) : VelocityField :=
  NSFormalization.Section3.T15.periodizedScaledVelocity P.velocity x₀ T ε

/-- The reconciled Spec's packet-argument spelling of the raw periodized
pressure. -/
def periodizedScaledPressure {nu : ℝ} (P : PacketImportAPI nu) (x₀ : Space)
    (T ε : ℝ) : PressureField :=
  NSFormalization.Section3.T15.periodizedScaledPressure P.pressure x₀ T ε

/-- The reconciled Spec's packet-argument spelling of the periodized force. -/
def periodizedScaledForce {nu : ℝ} (P : PacketImportAPI nu) (x₀ : Space)
    (T ε : ℝ) : VelocityField :=
  NSFormalization.Section3.T15.periodizedScaledForce P.force x₀ T ε

/-- The U1 prefix of `PeriodicInsertionAPI`, with the exact Spec field types
and order.  Its canonical placement/correction arguments are the outputs of
the fieldwise T15/T17 structure-exception conversions. -/
structure PeriodicInsertionU1API {nu : ℝ} (P : PacketImportAPI nu)
    (place : PlacementData P.toPacketAPI)
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta)) : Type where
  delta_pos : 0 < delta
  reference_force_mem : g ∈ forceClassT
  initial_mem : a ∈ initialClassT
  ε₀ : ℝ
  eps_pos : 0 < ε₀
  eps_le_scaling : ε₀ ≤ place.ε₀
  eps_le_cutoff : ε₀ ≤ D.ε₀
  velocity : ℝ → VelocityField
  pressure : ℝ → SpaceTimeScalar
  force : ℝ → VelocityField
  velocity_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    velocity ε z = reference.velocity z + D.correction ε z +
      periodizedScaledVelocity P place.x₀ place.T ε z
  pressure_formula : ∀ ε : ℝ,
    pressure ε = normalizePressureT
      (fun z ↦ reference.pressure z +
        periodizedScaledPressure P place.x₀ place.T ε z)
  force_formula : ∀ ε : ℝ, ∀ z : SpaceTime,
    force ε z = g z +
      correctionForce nu reference.velocity D ε z +
      periodizedScaledForce P place.x₀ place.T ε z

end Spec

/-- All seventeen placement fields, from the packet-projection Spec spelling
to T15's raw-field canonical spelling. -/
def placementOfSpec {nu : ℝ} {P : PacketAPI nu} (place : Spec.PlacementData P) :
    NSFormalization.Section3.T15.PlacementData
      P.velocity P.pressure P.force P.carrier :=
  { T := place.T
    time_pos := place.time_pos
    chartCenter := place.chartCenter
    chartRadius := place.chartRadius
    chartRadius_pos := place.chartRadius_pos
    chartBall_in_cube := place.chartBall_in_cube
    x₀ := place.x₀
    x₀_mem := place.x₀_mem
    Kstar := place.Kstar
    Kstar_compact := place.Kstar_compact
    carrier_subset := place.carrier_subset
    force_projection_subset := place.force_projection_subset
    ε₀ := place.ε₀
    eps_pos := place.eps_pos
    eps_le_one := place.eps_le_one
    eps_time := place.eps_time
    eps_space := place.eps_space }

/-- All seven cutoff data fields, from the Spec spelling to T16's canonical
spelling. -/
def cutoffOfSpec (D : Spec.CutoffData) : NSFormalization.Section3.T16.CutoffData :=
  D.toCanonical

/-- Fieldwise conversion of the Spec-threaded U1 inputs to the canonical
contract-free bundle. -/
def ofSpecInputs {nu : ℝ} (P : PacketImportAPI nu)
    (place : Spec.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI (ν := nu) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place))
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta))
    (correction : CorrectionAPI nu (placementOfSpec place) reference.velocity r delta
      (cutoffOfSpec D))
    (hdelta : 0 < delta) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    NSFormalization.Section3.T18.InsertionData :=
  { ν := nu
    packetVelocity := P.velocity
    packetPressure := P.pressure
    packetForce := P.force
    carrier := P.carrier
    energyBound := P.energyBound
    dissipationBound := P.dissipationBound
    place := placementOfSpec place
    scaling := scaling
    a := a
    g := g
    r := r
    δ := delta
    D := cutoffOfSpec D
    reference := BlowupDensity.Bindings.TorusLocalTheory.ofContract reference
    correction := correction
    hδ := hdelta
    hg := by
      simpa only [BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq] using hg
    ha := by
      simpa only [BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq] using ha }

/-- All eleven Spec-form U1 fields are discharged by the canonical U1
declarations after the packet and reference conversions above. -/
def insertionU1OfCanonical {nu : ℝ} (P : PacketImportAPI nu)
    (place : Spec.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI (ν := nu) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place))
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta))
    (correction : CorrectionAPI nu (placementOfSpec place) reference.velocity r delta
      (cutoffOfSpec D))
    (hdelta : 0 < delta) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    Spec.PeriodicInsertionU1API P place a g r delta D reference := by
  let data := ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha
  refine
    { delta_pos := NSFormalization.Section3.T18.delta_pos data
      reference_force_mem := ?_
      initial_mem := ?_
      ε₀ := NSFormalization.Section3.T18.ε₀ data
      eps_pos := NSFormalization.Section3.T18.eps_pos data
      eps_le_scaling := NSFormalization.Section3.T18.eps_le_scaling data
      eps_le_cutoff := NSFormalization.Section3.T18.eps_le_cutoff data
      velocity := NSFormalization.Section3.T18.velocity data
      pressure := NSFormalization.Section3.T18.pressure data
      force := NSFormalization.Section3.T18.force data
      velocity_formula := ?_
      pressure_formula := ?_
      force_formula := ?_ }
  · simpa only [data, ofSpecInputs,
      BlowupDensity.Bindings.TorusLocalTheory.forceClassT_eq] using
      NSFormalization.Section3.T18.reference_force_mem data
  · simpa only [data, ofSpecInputs,
      BlowupDensity.Bindings.TorusLocalTheory.initialClassT_eq] using
      NSFormalization.Section3.T18.initial_mem data
  · intro ε z
    exact NSFormalization.Section3.T18.velocity_formula data ε z
  · intro ε
    rw [BlowupDensity.Bindings.TorusLocalTheory.normalizePressureT_eq]
    exact NSFormalization.Section3.T18.pressure_formula data ε
  · intro ε z
    exact NSFormalization.Section3.T18.force_formula data ε z

namespace Spec

/-- The reconciled Spec's corrected background `b_ε = v + w_ε`, after the
fieldwise T16 data conversion. -/
def correctedBackground (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) : SpaceTimeField :=
  NSFormalization.Section3.T16.correctedBackground v D.correction ε

/-- Exactly the three U5/U6 field types, with the U1 data already chosen. -/
structure PeriodicInsertionU5U6Fields {nu : ℝ} (P : PacketImportAPI nu) (x₀ : Space)
    (T : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε₀ : ℝ)
    (velocity : ℝ → VelocityField) (pressure : ℝ → SpaceTimeScalar)
    (force : ℝ → VelocityField) : Prop where
  crossTransport_background_advects_packet : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (periodizedScaledVelocity P x₀ T ε) t x
          (correctedBackground v D ε (t, x)) = 0
  crossTransport_packet_advects_background : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
      spatialDerivative (correctedBackground v D ε) t x
          (periodizedScaledVelocity P x₀ T ε (t, x)) = 0
  momentum : ∀ ε ∈ Ioc (0 : ℝ) ε₀, ∀ t ∈ Ioo (0 : ℝ) T, ∀ x : Space,
    navierStokesResidual nu (velocity ε) (pressure ε) t x = force ε (t, x)

end Spec

/-- The two cross-transport fields and the exact momentum equation, in the
Spec's spelling, are discharged by the canonical U5/U6 declarations after the
packet, cutoff and reference conversions above. -/
theorem insertionU5U6OfCanonical {nu : ℝ} (P : PacketImportAPI nu)
    (place : Spec.PlacementData P.toPacketAPI)
    (scaling : ScalingAPI (ν := nu) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place))
    (a : SpatialField) (g : SpaceTimeField) (r delta : ℝ) (D : Spec.CutoffData)
    (reference : ClassicalSolutionT nu a g (place.T + delta))
    (correction : CorrectionAPI nu (placementOfSpec place) reference.velocity r delta
      (cutoffOfSpec D))
    (hdelta : 0 < delta) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    let U := insertionU1OfCanonical P place scaling a g r delta D reference correction hdelta hg ha
    Spec.PeriodicInsertionU5U6Fields P place.x₀ place.T reference.velocity D
      U.ε₀ U.velocity U.pressure U.force := by
  let data := ofSpecInputs P place scaling a g r delta D reference correction hdelta hg ha
  refine ⟨?_, ?_, ?_⟩
  · exact NSFormalization.Section3.T18.crossTransport_background_advects_packet data
  · exact NSFormalization.Section3.T18.crossTransport_packet_advects_background data
  · exact NSFormalization.Section3.T18.momentum data

end BlowupDensity.T18.U5U6ClosesProbe
