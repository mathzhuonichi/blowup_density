import Contracts.V1.Scaling3
import Bindings.PacketImport
import Bindings.TorusLocalTheory
import Bindings.Localization
import NSFormalization.Section3.T15.Assembly

noncomputable section
namespace BlowupDensity.Bindings.Scaling3
open Set MeasureTheory Filter Topology
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal

def placementOfSpec {ν : ℝ} {P : PacketAPI ν} (place : Contracts.V1.Scaling3.PlacementData P) :
    NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier where
  T := place.T
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
  eps_space := place.eps_space

theorem localizationOfSpec (h : LocalizationAPI) : NSFormalization.Section3.T13.LocalizationAPI where
  constant_pos_finite := h.constant_pos_finite
  wholeSpace_identity := h.wholeSpace_identity
  torus_identity := h.torus_identity
  localization := h.localization
  endpoint_zero := h.endpoint_zero
  endpoint_one := h.endpoint_one

def scalingOfSpec {ν : ℝ} {P : PacketImportAPI ν} {place : Contracts.V1.Scaling3.PlacementData P.toPacketAPI}
    (h : Contracts.V1.Scaling3.ScalingAPI P place) :
    NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place) where
  localization := localizationOfSpec h.localization
  velocity_summable := h.velocity_summable
  pressure_summable := h.pressure_summable
  force_summable := h.force_summable
  velocity_singleCopy := h.velocity_singleCopy
  pressure_singleCopy := h.pressure_singleCopy
  force_singleCopy := h.force_singleCopy
  force_mem := h.force_mem
  solution := by
    intro ε hε
    obtain ⟨w, hv, hp⟩ := h.solution ε hε
    exact ⟨Bindings.TorusLocalTheory.ofContract w, hv, hp⟩
  pressureSlice_integrable := h.pressureSlice_integrable
  unboundedSpeed := h.unboundedSpeed
  energySlices_memLp := h.energySlices_memLp
  packetEnergyIdentity := h.packetEnergyIdentity
  packetDissipationIdentity := h.packetDissipationIdentity
  mixed_memLp := h.mixed_memLp
  packetMixedScaling := h.packetMixedScaling
  sobolevConst := h.sobolevConst
  sobolevConst_pos := h.sobolevConst_pos
  forceSobolev_memLp := h.forceSobolev_memLp
  packetSobolevBound := h.packetSobolevBound
  forceConvergence := h.forceConvergence

def placementToSpec {ν : ℝ} {P : PacketAPI ν} (h : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier) : Contracts.V1.Scaling3.PlacementData P where
  T := h.T
  time_pos := h.time_pos
  chartCenter := h.chartCenter
  chartRadius := h.chartRadius
  chartRadius_pos := h.chartRadius_pos
  chartBall_in_cube := h.chartBall_in_cube
  x₀ := h.x₀
  x₀_mem := h.x₀_mem
  Kstar := h.Kstar
  Kstar_compact := h.Kstar_compact
  carrier_subset := h.carrier_subset
  force_projection_subset := h.force_projection_subset
  ε₀ := h.ε₀
  eps_pos := h.eps_pos
  eps_le_one := h.eps_le_one
  eps_time := h.eps_time
  eps_space := h.eps_space

theorem placement_to_of {ν : ℝ} {P : PacketAPI ν} (h : Contracts.V1.Scaling3.PlacementData P) :
    placementToSpec (placementOfSpec h) = h := rfl

theorem placement_of_to {ν : ℝ} {P : PacketAPI ν} (h : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier) :
    placementOfSpec (placementToSpec h) = h := rfl

def scalingToSpec {ν : ℝ} {P : PacketImportAPI ν} {place : Contracts.V1.Scaling3.PlacementData P.toPacketAPI} (h : NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place)) : Contracts.V1.Scaling3.ScalingAPI P place where
  localization := ⟨h.localization.constant_pos_finite, h.localization.wholeSpace_identity, h.localization.torus_identity, h.localization.localization, h.localization.endpoint_zero, h.localization.endpoint_one⟩
  velocity_summable := h.velocity_summable
  pressure_summable := h.pressure_summable
  force_summable := h.force_summable
  velocity_singleCopy := h.velocity_singleCopy
  pressure_singleCopy := h.pressure_singleCopy
  force_singleCopy := h.force_singleCopy
  force_mem := h.force_mem
  solution := by
    intro ε hε
    obtain ⟨w, hv, hp⟩ := h.solution ε hε
    exact ⟨Bindings.TorusLocalTheory.toContract w, hv, hp⟩
  pressureSlice_integrable := h.pressureSlice_integrable
  unboundedSpeed := h.unboundedSpeed
  energySlices_memLp := h.energySlices_memLp
  packetEnergyIdentity := h.packetEnergyIdentity
  packetDissipationIdentity := h.packetDissipationIdentity
  mixed_memLp := h.mixed_memLp
  packetMixedScaling := h.packetMixedScaling
  sobolevConst := h.sobolevConst
  sobolevConst_pos := h.sobolevConst_pos
  forceSobolev_memLp := h.forceSobolev_memLp
  packetSobolevBound := h.packetSobolevBound
  forceConvergence := h.forceConvergence

theorem scaling_to_of {ν : ℝ} {P : PacketImportAPI ν} {place : Contracts.V1.Scaling3.PlacementData P.toPacketAPI} (h : Contracts.V1.Scaling3.ScalingAPI P place) :
    scalingToSpec (scalingOfSpec h) = h := rfl

theorem scaling_of_to {ν : ℝ} {P : PacketImportAPI ν} {place : Contracts.V1.Scaling3.PlacementData P.toPacketAPI} (h : NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place)) :
    scalingOfSpec (scalingToSpec h) = h := rfl

theorem scaledStartTime_eq : @Contracts.V1.Scaling3.scaledStartTime = @NSFormalization.Section3.T15.scaledStartTime := rfl
theorem scaledSourcePoint_eq : @Contracts.V1.Scaling3.scaledSourcePoint = @NSFormalization.Section3.T15.scaledSourcePoint := rfl
theorem scaledVelocity_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.scaledVelocity P = NSFormalization.Section3.T15.scaledVelocity P.velocity := rfl
theorem scaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.scaledPressure P = NSFormalization.Section3.T15.scaledPressure P.pressure := rfl
theorem scaledForce_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.scaledForce P = NSFormalization.Section3.T15.scaledForce P.force := rfl
theorem periodizedScaledVelocity_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.periodizedScaledVelocity P = NSFormalization.Section3.T15.periodizedScaledVelocity P.velocity := rfl
theorem periodizedScaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.periodizedScaledPressure P = NSFormalization.Section3.T15.periodizedScaledPressure P.pressure := rfl
theorem periodizedScaledForce_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.periodizedScaledForce P = NSFormalization.Section3.T15.periodizedScaledForce P.force := rfl
theorem normalizedScaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν) :
    Contracts.V1.Scaling3.normalizedScaledPressure P = NSFormalization.Section3.T15.normalizedScaledPressure P.pressure := rfl
theorem IsPeriodicLebesgueSlicePath_eq : @Contracts.V1.Scaling3.IsPeriodicLebesgueSlicePath = @NSFormalization.Section3.T15.IsPeriodicLebesgueSlicePath := rfl
theorem mixedLebesgueENormT_eq : @Contracts.V1.Scaling3.mixedLebesgueENormT = @NSFormalization.Section3.T15.mixedLebesgueENormT := rfl
theorem MemMixedLebesgueR_eq : @Contracts.V1.Scaling3.MemMixedLebesgueR = @NSFormalization.Section3.T15.MemMixedLebesgueR := rfl
theorem MemMixedLebesgueT_eq : @Contracts.V1.Scaling3.MemMixedLebesgueT = @NSFormalization.Section3.T15.MemMixedLebesgueT := rfl
theorem MemForceSobolevT_eq : @Contracts.V1.Scaling3.MemForceSobolevT = @NSFormalization.Section3.T15.MemForceSobolevT := rfl
theorem EnergySlicesMemLpT_eq : @Contracts.V1.Scaling3.EnergySlicesMemLpT = @NSFormalization.Section3.T15.EnergySlicesMemLpT := rfl
theorem alphaT_eq : @Contracts.V1.Scaling3.alphaT = @NSFormalization.Section3.T15.alphaT := rfl

/-- Structure-exception bridge for the statement: the same quantified packet
family and placement, with only the API converted fieldwise. -/
theorem scalingStatement_iff : Contracts.V1.Scaling3.scalingStatement ↔
    ∀ (𝔉 : PacketImportFamily) (ν : ℝ) (hν : 0 < ν)
      (place : Contracts.V1.Scaling3.PlacementData (𝔉.select ν hν).toPacketAPI),
      Nonempty (NSFormalization.Section3.T15.ScalingAPI (ν := ν)
        (𝔉.select ν hν).velocity (𝔉.select ν hν).pressure (𝔉.select ν hν).force
        (𝔉.select ν hν).carrier (𝔉.select ν hν).energyBound
        (𝔉.select ν hν).dissipationBound (placementOfSpec place)) := by
  constructor
  · intro h 𝔉 ν hν place
    exact (h 𝔉 ν hν place).map scalingOfSpec
  · intro h 𝔉 ν hν place
    exact (h 𝔉 ν hν place).map scalingToSpec

/-- Canonical placement at the prescribed reference horizon. -/
def placementData {ν : ℝ} (P : PacketAPI ν) (T : ℝ) (hT : 0 < T) :
    Contracts.V1.Scaling3.PlacementData P :=
  placementToSpec (NSFormalization.Section3.T15.placementData P.carrier_compact
    P.force_support.1 T hT)

theorem placementData_time {ν : ℝ} (P : PacketAPI ν) (T : ℝ) (hT : 0 < T) :
    (placementData P T hT).T = T := rfl

/-- Every energy-enhanced packet, and every fixed admissible placement. -/
def scalingAPI {ν : ℝ} (P : PacketImportAPI ν)
    (place : Contracts.V1.Scaling3.PlacementData P.toPacketAPI) :
    Contracts.V1.Scaling3.ScalingAPI P place :=
  scalingToSpec (NSFormalization.Section3.T15.scalingAPI
    ⟨P.velocity_extension_smooth, P.carrier_compact, P.velocity_support,
      P.square_integrable, P.zero_initial_velocity, P.energy_isLUB,
      P.dissipation_integrable, P.dissipation_eq⟩ P.pressure_support P.pressure_extension_smooth
    P.force_smooth P.force_support P.force_zero_nonpos P.extension_navier_stokes
    P.extension_divergence_free P.speed_unbounded (placementOfSpec place))

/-- The literal reconciled quantifier order, including arbitrary packet family. -/
theorem scalingStatement_holds : Contracts.V1.Scaling3.scalingStatement := by
  intro 𝔉 ν hν place
  exact ⟨scalingAPI (𝔉.select ν hν) place⟩

/-- Instance whose underlying packet is exactly the registered I01 choice. -/
def scalingPacket (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 < T) :
    Contracts.V1.Scaling3.ScalingAPI (Bindings.packetImportFamily.select ν hν)
      (placementData (Bindings.packet ν hν) T hT) :=
  scalingAPI _ _

end BlowupDensity.Bindings.Scaling3
