import Contracts.V1.PeriodicInsertion
import NSFormalization.Section3.T18.Assembly
import Bindings.TorusLocalTheory
import Bindings.LocalPotential
import Bindings.Localization
import Bindings.DatumLemmas

/-! Fieldwise structure-exception adapters and U1–U11 assembly.
The placement/reference conversion and raw packet discharge follow the seven
research/T18/probes/*_closes.lean conformance probes. -/
noncomputable section
namespace BlowupDensity.Bindings.PeriodicInsertion
open Set MeasureTheory Filter Topology
open Contracts.V1 Contracts.V1.Data Contracts.V1.TorusData Contracts.V1.TorusLocalTheory
open scoped ENNReal




def placementOfSpec {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.Draft.PlacementData P) :
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

theorem potentialOfSpec {v U : SpaceTimeField} {K : Set Space} {x₀ : Space} {r T δ : ℝ}
    {D : CutoffData} (h : LocalPotentialAPI v U K x₀ r T δ D) :
    NSFormalization.Section3.T16.LocalPotentialAPI v U K x₀ r T δ (Bindings.CutoffData.ofContract D) where
  theta_smooth := h.theta_smooth
  theta_compactSupport := h.theta_compactSupport
  theta_range := h.theta_range
  plateau_open := h.plateau_open
  prescribed_subset_plateau := h.prescribed_subset_plateau
  theta_one := h.theta_one
  theta_radius_pos := h.theta_radius_pos
  theta_support := h.theta_support
  eta_smooth := h.eta_smooth
  eta_compactSupport := h.eta_compactSupport
  eta_range := h.eta_range
  eta_one := h.eta_one
  eta_support := h.eta_support
  eps_pos := h.eps_pos
  eps_time := h.eps_time
  eps_space := h.eps_space
  potential_smooth := h.potential_smooth
  potential_formula := h.potential_formula
  potential_curl := h.potential_curl
  correction_formula := h.correction_formula
  correction_smooth := h.correction_smooth
  correction_periodic := h.correction_periodic
  correction_divergence_free := h.correction_divergence_free
  correction_support := h.correction_support
  correction_support_ball := h.correction_support_ball
  correction_cancels := h.correction_cancels

def scalingOfSpec {ν : ℝ} {P : PacketImportAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI}
    (h : BlowupDensity.T15.Draft.ScalingAPI P place) :
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

def correctionOfSpec {ν : ℝ} {P : PacketAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : CutoffData}
    (h : BlowupDensity.T17.Spec.CorrectionAPI ν place v r δ D) :
    NSFormalization.Section3.T17.CorrectionAPI ν (placementOfSpec place) v r δ (Bindings.CutoffData.ofContract D) where
  potential := potentialOfSpec h.potential
  localization := localizationOfSpec h.localization
  viscosity_pos := h.viscosity_pos
  radius_pos := h.radius_pos
  ball_in_chart := h.ball_in_chart
  eps_le_placement := h.eps_le_placement
  reference_periodic := h.reference_periodic
  correction_profile_smooth := h.correction_profile_smooth
  correction_profile_support := h.correction_profile_support
  correctionProfileConst := h.correctionProfileConst
  correctionProfileConst_nonneg := h.correctionProfileConst_nonneg
  correction_profile_uniform := h.correction_profile_uniform
  force_profile_smooth := h.force_profile_smooth
  force_profile_support := h.force_profile_support
  forceProfileConst := h.forceProfileConst
  forceProfileConst_nonneg := h.forceProfileConst_nonneg
  force_profile_uniform := h.force_profile_uniform
  correction_profile_identity := h.correction_profile_identity
  force_profile_identity := h.force_profile_identity
  force_smooth := h.force_smooth
  force_periodic := h.force_periodic
  force_support := h.force_support
  spatialVolumeConst := h.spatialVolumeConst
  spatialVolumeConst_nonneg := h.spatialVolumeConst_nonneg
  force_spatial_volume := h.force_spatial_volume
  force_time_length := h.force_time_length
  correctionDerivConst := h.correctionDerivConst
  correctionDerivConst_nonneg := h.correctionDerivConst_nonneg
  correction_derivative_bound := h.correction_derivative_bound
  forceDerivConst := h.forceDerivConst
  forceDerivConst_nonneg := h.forceDerivConst_nonneg
  force_derivative_bound := h.force_derivative_bound
  correction_slice_memLp := h.correction_slice_memLp
  correction_gradient_memLp := h.correction_gradient_memLp
  energyConst := h.energyConst
  energyConst_nonneg := h.energyConst_nonneg
  correction_energy_bound := h.correction_energy_bound
  force_spatial_memLp := h.force_spatial_memLp
  mixedConst := h.mixedConst
  mixedConst_nonneg := h.mixedConst_nonneg
  force_mixed_bound := h.force_mixed_bound
  sobolevConst := h.sobolevConst
  sobolevConst_pos := h.sobolevConst_pos
  forceSobolev_memLp := h.forceSobolev_memLp
  force_sobolev_bound := h.force_sobolev_bound

def ofSpecInputs {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) : NSFormalization.Section3.T18.InsertionData where
  ν := ν
  packetVelocity := P.velocity
  packetPressure := P.pressure
  packetForce := P.force
  carrier := P.carrier
  energyBound := P.energyBound
  dissipationBound := P.dissipationBound
  place := placementOfSpec place
  scaling := scalingOfSpec scaling
  a := a
  g := g
  r := r
  δ := δ
  D := Bindings.CutoffData.ofContract D
  reference := Bindings.TorusLocalTheory.ofContract reference
  correction := correctionOfSpec correction
  hδ := hδ
  hg := hg
  ha := ha

theorem packet_energyBound_nonneg {nu : ℝ} (P : PacketImportAPI nu) :
    0 ≤ P.energyBound := by
  have hmem : Real.sqrt (NavierStokesR3.CompactEnergy.l2Sq P.velocity 0) ∈
      (fun t : ℝ => Real.sqrt (NavierStokesR3.CompactEnergy.l2Sq P.velocity t)) ''
        Ico (0 : ℝ) 1 := ⟨0, ⟨le_rfl, zero_lt_one⟩, rfl⟩
  exact (Real.sqrt_nonneg _).trans (P.energy_isLUB.1 hmem)

/-- The Spec packet's exact dissipation formula makes `D` nonnegative. -/
theorem packet_dissipationBound_nonneg {nu : ℝ} (P : PacketImportAPI nu) :
    0 ≤ P.dissipationBound := by
  rw [P.dissipation_eq]
  exact Real.sqrt_nonneg _

/-- The structure exception for all 45 fields, canonical to contract. -/
def toSpecAPI {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)
    (h : NSFormalization.Section3.T18.PeriodicInsertionAPI (ofSpecInputs P place scaling a g r δ D reference correction hδ hg ha)) :
    BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction := by
  exact {
    delta_pos := h.delta_pos
    reference_force_mem := h.reference_force_mem
    initial_mem := h.initial_mem
    ε₀ := h.ε₀
    eps_pos := h.eps_pos
    eps_le_scaling := h.eps_le_scaling
    eps_le_cutoff := h.eps_le_cutoff
    velocity := h.velocity
    pressure := h.pressure
    force := h.force
    velocity_formula := h.velocity_formula
    pressure_formula := h.pressure_formula
    force_formula := h.force_formula
    force_mem := h.force_mem
    forceDifference_mem := h.forceDifference_mem
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    initial := h.initial
    incompressible := h.incompressible
    momentum := h.momentum
    history := h.history
    velocity_periodic := h.velocity_periodic
    solution := by
      intro ε hε
      obtain ⟨w, hv, hp⟩ := h.solution ε hε
      exact ⟨Bindings.TorusLocalTheory.toContract w, hv, hp⟩
    maximal := by
      intro ε hε
      rw [Bindings.TorusLocalTheory.isMaximalPeriodicSolution_eq]
      exact h.maximal ε hε
    lifespan := by
      intro ε hε
      rw [Bindings.TorusLocalTheory.maximalLifespanT_eq]
      exact h.lifespan ε hε
    blowup := h.blowup
    blowup_limsup := h.blowup_limsup
    crossTransport_background_advects_packet := h.crossTransport_background_advects_packet
    crossTransport_packet_advects_background := h.crossTransport_packet_advects_background
    velocityDifference_divFree := h.velocityDifference_divFree
    diffSupportRadius := h.diffSupportRadius
    diffSupportRadius_pos := h.diffSupportRadius_pos
    velocityDifference_support := h.velocityDifference_support
    diffSupport_in_chart := h.diffSupport_in_chart
    energyRate := h.energyRate
    forceDiffMixedConst := h.forceDiffMixedConst
    forceDiffMixedConst_nonneg := h.forceDiffMixedConst_nonneg
    forceDifference_mixed_memLp := h.forceDifference_mixed_memLp
    forceDifference_mixed_bound := h.forceDifference_mixed_bound
    forceDiffSobolevConst := h.forceDiffSobolevConst
    forceDiffSobolevConst_pos := h.forceDiffSobolevConst_pos
    forceDifference_sobolev_memLp := h.forceDifference_sobolev_memLp
    forceDifference_sobolev_bound := h.forceDifference_sobolev_bound
    forceDifference_negativeSobolev_tendsto := h.forceDifference_negativeSobolev_tendsto
    negative_s_memLp := h.negative_s_memLp
  }
/-- The inverse conversion, with the registered T11 predicates rewritten. -/
def ofSpecAPI {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)
    (h : BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction) :
    NSFormalization.Section3.T18.PeriodicInsertionAPI (ofSpecInputs P place scaling a g r δ D reference correction hδ hg ha) := by
  exact {
    delta_pos := h.delta_pos
    reference_force_mem := h.reference_force_mem
    initial_mem := h.initial_mem
    ε₀ := h.ε₀
    eps_pos := h.eps_pos
    eps_le_scaling := h.eps_le_scaling
    eps_le_cutoff := h.eps_le_cutoff
    velocity := h.velocity
    pressure := h.pressure
    force := h.force
    velocity_formula := h.velocity_formula
    pressure_formula := h.pressure_formula
    force_formula := h.force_formula
    force_mem := h.force_mem
    forceDifference_mem := h.forceDifference_mem
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    initial := h.initial
    incompressible := h.incompressible
    momentum := h.momentum
    history := h.history
    velocity_periodic := h.velocity_periodic
    solution := by
      intro ε hε
      obtain ⟨w, hv, hp⟩ := h.solution ε hε
      exact ⟨Bindings.TorusLocalTheory.ofContract w, hv, hp⟩
    maximal := by
      intro ε hε
      have hw := h.maximal ε hε
      rw [Bindings.TorusLocalTheory.isMaximalPeriodicSolution_eq] at hw
      exact hw
    lifespan := by
      intro ε hε
      have hw := h.lifespan ε hε
      rw [Bindings.TorusLocalTheory.maximalLifespanT_eq] at hw
      exact hw
    blowup := h.blowup
    blowup_limsup := h.blowup_limsup
    crossTransport_background_advects_packet := h.crossTransport_background_advects_packet
    crossTransport_packet_advects_background := h.crossTransport_packet_advects_background
    velocityDifference_divFree := h.velocityDifference_divFree
    diffSupportRadius := h.diffSupportRadius
    diffSupportRadius_pos := h.diffSupportRadius_pos
    velocityDifference_support := h.velocityDifference_support
    diffSupport_in_chart := h.diffSupport_in_chart
    energyRate := h.energyRate
    forceDiffMixedConst := h.forceDiffMixedConst
    forceDiffMixedConst_nonneg := h.forceDiffMixedConst_nonneg
    forceDifference_mixed_memLp := h.forceDifference_mixed_memLp
    forceDifference_mixed_bound := h.forceDifference_mixed_bound
    forceDiffSobolevConst := h.forceDiffSobolevConst
    forceDiffSobolevConst_pos := h.forceDiffSobolevConst_pos
    forceDifference_sobolev_memLp := h.forceDifference_sobolev_memLp
    forceDifference_sobolev_bound := h.forceDifference_sobolev_bound
    forceDifference_negativeSobolev_tendsto := h.forceDifference_negativeSobolev_tendsto
    negative_s_memLp := h.negative_s_memLp
  }

theorem api_to_of {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)
    (h : BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction) :
    toSpecAPI P place scaling a g r δ D reference correction hδ hg ha (ofSpecAPI P place scaling a g r δ D reference correction hδ hg ha h) = h := rfl

theorem api_of_to {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)
    (h : NSFormalization.Section3.T18.PeriodicInsertionAPI (ofSpecInputs P place scaling a g r δ D reference correction hδ hg ha)) :
    ofSpecAPI P place scaling a g r δ D reference correction hδ hg ha (toSpecAPI P place scaling a g r δ D reference correction hδ hg ha h) = h := rfl

def periodicInsertion {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT) :
    BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction := by
  let data := ofSpecInputs P place scaling a g r δ D reference correction hδ hg ha
  let hraw : NSFormalization.Section3.T18.RawPremises data :=
    ⟨P.velocity_support, packet_energyBound_nonneg P, packet_dissipationBound_nonneg P⟩
  let h := NSFormalization.Section3.T18.assemble data hraw
  exact toSpecAPI P place scaling a g r δ D reference correction hδ hg ha h

theorem periodicInsertionStatement_holds : BlowupDensity.T18.Spec.periodicInsertionStatement := by
  intro ν _ P place scaling a g r δ D reference correction hδ hg ha
  exact ⟨periodicInsertion P place scaling a g r δ D reference correction hδ hg ha⟩


/-! Definitional bridges for every restated physical or norm definition. -/
theorem scaledStartTime_eq : @BlowupDensity.T15.Draft.scaledStartTime = @NSFormalization.Section3.T15.scaledStartTime := rfl
theorem scaledSourcePoint_eq : @BlowupDensity.T15.Draft.scaledSourcePoint = @NSFormalization.Section3.T15.scaledSourcePoint := rfl
theorem IsPeriodicLebesgueSlicePath_eq : @BlowupDensity.T15.Draft.IsPeriodicLebesgueSlicePath = @NSFormalization.Section3.T15.IsPeriodicLebesgueSlicePath := rfl
theorem mixedLebesgueENormT_eq : @BlowupDensity.T15.Draft.mixedLebesgueENormT = @NSFormalization.Section3.T15.mixedLebesgueENormT := rfl
theorem MemMixedLebesgueR_eq : @BlowupDensity.T15.Draft.MemMixedLebesgueR = @NSFormalization.Section3.T15.MemMixedLebesgueR := rfl
theorem MemMixedLebesgueT_eq : @BlowupDensity.T15.Draft.MemMixedLebesgueT = @NSFormalization.Section3.T15.MemMixedLebesgueT := rfl
theorem MemForceSobolevT_eq : @BlowupDensity.T15.Draft.MemForceSobolevT = @NSFormalization.Section3.T15.MemForceSobolevT := rfl
theorem EnergySlicesMemLpT_eq : @BlowupDensity.T15.Draft.EnergySlicesMemLpT = @NSFormalization.Section3.T15.EnergySlicesMemLpT := rfl
theorem alphaT_eq : @BlowupDensity.T15.Draft.alphaT = @NSFormalization.Section3.T15.alphaT := rfl
theorem scaledVelocity_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.scaledVelocity P = NSFormalization.Section3.T15.scaledVelocity P.velocity := rfl
theorem scaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.scaledPressure P = NSFormalization.Section3.T15.scaledPressure P.pressure := rfl
theorem scaledForce_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.scaledForce P = NSFormalization.Section3.T15.scaledForce P.force := rfl
theorem periodizedScaledVelocity_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.periodizedScaledVelocity P = NSFormalization.Section3.T15.periodizedScaledVelocity P.velocity := rfl
theorem periodizedScaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.periodizedScaledPressure P = NSFormalization.Section3.T15.periodizedScaledPressure P.pressure := rfl
theorem periodizedScaledForce_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.periodizedScaledForce P = NSFormalization.Section3.T15.periodizedScaledForce P.force := rfl
theorem normalizedScaledPressure_eq {ν : ℝ} (P : PacketImportAPI ν) :
    BlowupDensity.T15.Draft.normalizedScaledPressure P = NSFormalization.Section3.T15.normalizedScaledPressure P.pressure := rfl
theorem torusSpaceTimeLift_eq : @BlowupDensity.T17.Spec.torusSpaceTimeLift = @NSFormalization.Section3.T17.torusSpaceTimeLift := rfl
theorem torusSpatialSupport_eq : @BlowupDensity.T17.Spec.torusSpatialSupport = @NSFormalization.Section3.T17.torusSpatialSupport := rfl
theorem torusTemporalSupport_eq : @BlowupDensity.T17.Spec.torusTemporalSupport = @NSFormalization.Section3.T17.torusTemporalSupport := rfl
theorem fixedProfileCylinder_eq (D : CutoffData) :
    BlowupDensity.T17.Spec.fixedProfileCylinder D = NSFormalization.Section3.T17.fixedProfileCylinder (Bindings.CutoffData.ofContract D) := rfl
theorem correctionForce_eq (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) :
    BlowupDensity.T17.Spec.correctionForce ν v D = NSFormalization.Section3.T17.correctionForce ν v (Bindings.CutoffData.ofContract D) := rfl
theorem correctionChartPoint_eq {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.Draft.PlacementData P) :
    BlowupDensity.T17.Spec.correctionChartPoint place = NSFormalization.Section3.T17.correctionChartPoint place.x₀ place.T := rfl
theorem rescaledReference_eq {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.Draft.PlacementData P) (v : SpaceTimeField) :
    BlowupDensity.T17.Spec.rescaledReference v place = NSFormalization.Section3.T17.rescaledReference v place.x₀ place.T := rfl
theorem rescaledPotential_eq {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.Draft.PlacementData P) (v : SpaceTimeField) :
    BlowupDensity.T17.Spec.rescaledPotential v place = NSFormalization.Section3.T17.rescaledPotential v place.x₀ place.T := rfl
theorem rescaledCorrectionProfile_eq {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.Draft.PlacementData P) (v : SpaceTimeField) (ε : ℝ) (D : CutoffData) :
    BlowupDensity.T17.Spec.rescaledCorrectionProfile v place ε D = NSFormalization.Section3.T17.rescaledCorrectionProfile v place.x₀ place.T ε (Bindings.CutoffData.ofContract D) := rfl
theorem rescaledForceProfile_eq {ν : ℝ} {P : PacketAPI ν} (place : BlowupDensity.T15.Draft.PlacementData P) (v : SpaceTimeField) (ε : ℝ) (D : CutoffData) :
    BlowupDensity.T17.Spec.rescaledForceProfile ν v place ε D = NSFormalization.Section3.T17.rescaledForceProfile ν v place.x₀ place.T ε (Bindings.CutoffData.ofContract D) := rfl

def placementToSpec {ν : ℝ} {P : PacketAPI ν} (h : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier) : BlowupDensity.T15.Draft.PlacementData P where
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

theorem placement_to_of {ν : ℝ} {P : PacketAPI ν} (h : BlowupDensity.T15.Draft.PlacementData P) :
    placementToSpec (placementOfSpec h) = h := rfl

theorem placement_of_to {ν : ℝ} {P : PacketAPI ν} (h : NSFormalization.Section3.T15.PlacementData P.velocity P.pressure P.force P.carrier) :
    placementOfSpec (placementToSpec h) = h := rfl

def scalingToSpec {ν : ℝ} {P : PacketImportAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI} (h : NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place)) : BlowupDensity.T15.Draft.ScalingAPI P place where
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

theorem scaling_to_of {ν : ℝ} {P : PacketImportAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI} (h : BlowupDensity.T15.Draft.ScalingAPI P place) :
    scalingToSpec (scalingOfSpec h) = h := rfl

theorem scaling_of_to {ν : ℝ} {P : PacketImportAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI} (h : NSFormalization.Section3.T15.ScalingAPI (ν := ν) P.velocity P.pressure P.force P.carrier
      P.energyBound P.dissipationBound (placementOfSpec place)) :
    scalingOfSpec (scalingToSpec h) = h := rfl

def correctionToSpec {ν : ℝ} {P : PacketAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : CutoffData} (h : NSFormalization.Section3.T17.CorrectionAPI ν (placementOfSpec place) v r δ (Bindings.CutoffData.ofContract D)) : BlowupDensity.T17.Spec.CorrectionAPI ν place v r δ D where
  potential := Bindings.api_toContract h.potential
  localization := ⟨h.localization.constant_pos_finite, h.localization.wholeSpace_identity, h.localization.torus_identity, h.localization.localization, h.localization.endpoint_zero, h.localization.endpoint_one⟩
  viscosity_pos := h.viscosity_pos
  radius_pos := h.radius_pos
  ball_in_chart := h.ball_in_chart
  eps_le_placement := h.eps_le_placement
  reference_periodic := h.reference_periodic
  correction_profile_smooth := h.correction_profile_smooth
  correction_profile_support := h.correction_profile_support
  correctionProfileConst := h.correctionProfileConst
  correctionProfileConst_nonneg := h.correctionProfileConst_nonneg
  correction_profile_uniform := h.correction_profile_uniform
  force_profile_smooth := h.force_profile_smooth
  force_profile_support := h.force_profile_support
  forceProfileConst := h.forceProfileConst
  forceProfileConst_nonneg := h.forceProfileConst_nonneg
  force_profile_uniform := h.force_profile_uniform
  correction_profile_identity := h.correction_profile_identity
  force_profile_identity := h.force_profile_identity
  force_smooth := h.force_smooth
  force_periodic := h.force_periodic
  force_support := h.force_support
  spatialVolumeConst := h.spatialVolumeConst
  spatialVolumeConst_nonneg := h.spatialVolumeConst_nonneg
  force_spatial_volume := h.force_spatial_volume
  force_time_length := h.force_time_length
  correctionDerivConst := h.correctionDerivConst
  correctionDerivConst_nonneg := h.correctionDerivConst_nonneg
  correction_derivative_bound := h.correction_derivative_bound
  forceDerivConst := h.forceDerivConst
  forceDerivConst_nonneg := h.forceDerivConst_nonneg
  force_derivative_bound := h.force_derivative_bound
  correction_slice_memLp := h.correction_slice_memLp
  correction_gradient_memLp := h.correction_gradient_memLp
  energyConst := h.energyConst
  energyConst_nonneg := h.energyConst_nonneg
  correction_energy_bound := h.correction_energy_bound
  force_spatial_memLp := h.force_spatial_memLp
  mixedConst := h.mixedConst
  mixedConst_nonneg := h.mixedConst_nonneg
  force_mixed_bound := h.force_mixed_bound
  sobolevConst := h.sobolevConst
  sobolevConst_pos := h.sobolevConst_pos
  forceSobolev_memLp := h.forceSobolev_memLp
  force_sobolev_bound := h.force_sobolev_bound

theorem correction_to_of {ν : ℝ} {P : PacketAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : CutoffData} (h : BlowupDensity.T17.Spec.CorrectionAPI ν place v r δ D) :
    correctionToSpec (correctionOfSpec h) = h := rfl

theorem correction_of_to {ν : ℝ} {P : PacketAPI ν} {place : BlowupDensity.T15.Draft.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : CutoffData} (h : NSFormalization.Section3.T17.CorrectionAPI ν (placementOfSpec place) v r δ (Bindings.CutoffData.ofContract D)) :
    correctionOfSpec (correctionToSpec h) = h := rfl


/-- T17's placement spelling is precisely the shared T15 record. -/
theorem correctionPlacement_eq {ν : ℝ} (P : PacketAPI ν) :
    BlowupDensity.T17.Spec.PlacementData P = BlowupDensity.T15.Draft.PlacementData P := rfl

/-- Staged end-to-end non-vacuity. The witnesses still required are a full
T15 scaling record and a compatible T17 correction/reference triple.
No such witness is inferred from this conditional statement. -/
theorem nonvacuity_of_witnesses {ν : ℝ} (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT)
    (hw : ∃ _scaling : BlowupDensity.T15.Draft.ScalingAPI P place,
      ∃ reference : ClassicalSolutionT ν a g (place.T + δ),
        Nonempty (BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)) :
    Nonempty (Σ scaling : BlowupDensity.T15.Draft.ScalingAPI P place,
      Σ reference : ClassicalSolutionT ν a g (place.T + δ),
      Σ correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D,
        BlowupDensity.T18.Spec.PeriodicInsertionAPI ν P place scaling a g r δ D reference correction) := by
  obtain ⟨scaling, reference, ⟨correction⟩⟩ := hw
  exact ⟨⟨scaling, reference, correction,
    periodicInsertion P place scaling a g r δ D reference correction hδ hg ha⟩⟩

/-- Fieldwise statement bridge: the only difference is the separately
restated structure, transported by the inverse adapters above. -/
theorem periodicInsertionStatement_iff :
    BlowupDensity.T18.Spec.periodicInsertionStatement ↔
    ∀ (ν : ℝ) (_hν : 0 < ν) (P : PacketImportAPI ν)
    (place : BlowupDensity.T15.Draft.PlacementData P.toPacketAPI) (scaling : BlowupDensity.T15.Draft.ScalingAPI P place)
    (a : SpatialField) (g : SpaceTimeField) (r δ : ℝ) (D : CutoffData)
    (reference : ClassicalSolutionT ν a g (place.T + δ))
    (correction : BlowupDensity.T17.Spec.CorrectionAPI ν place reference.velocity r δ D)
    (hδ : 0 < δ) (hg : g ∈ forceClassT) (ha : a ∈ initialClassT),
      Nonempty (NSFormalization.Section3.T18.PeriodicInsertionAPI
        (ofSpecInputs P place scaling a g r δ D reference correction hδ hg ha)) := by
  constructor
  · intro h ν hν P place scaling a g r δ D reference correction hδ hg ha
    obtain ⟨A⟩ := h ν hν P place scaling a g r δ D reference correction hδ hg ha
    exact ⟨ofSpecAPI P place scaling a g r δ D reference correction hδ hg ha A⟩
  · intro h ν hν P place scaling a g r δ D reference correction hδ hg ha
    obtain ⟨A⟩ := h ν hν P place scaling a g r δ D reference correction hδ hg ha
    exact ⟨toSpecAPI P place scaling a g r δ D reference correction hδ hg ha A⟩

end BlowupDensity.Bindings.PeriodicInsertion
