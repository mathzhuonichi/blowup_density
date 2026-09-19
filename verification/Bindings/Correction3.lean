import Contracts.V1.Correction3
import Bindings.LocalPotential
import Bindings.Localization
import NSFormalization.Section3.T17.Assembly

/-! Definitional vocabulary bridges and fieldwise record conversions for T17.
Both raw-field and verbatim packet-indexed spellings retain all 45 fields. -/
noncomputable section
namespace BlowupDensity.Bindings.Correction3
open Set MeasureTheory
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal Topology BigOperators

def placementOfContract {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : Contracts.V1.Correction3.PlacementData u p f K) :
    NSFormalization.Section3.T15.PlacementData
      u p f K :=
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

def placementToContract {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData
      u p f K) :
    Contracts.V1.Correction3.PlacementData u p f K :=
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

theorem placementToContract_ofSpec {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : Contracts.V1.Correction3.PlacementData u p f K) :
    placementToContract (placementOfContract place) = place := rfl

theorem placementOfContract_toSpec {u : VelocityField} {p : PressureField} {f : VelocityField} {K : Set Space}
    (place : NSFormalization.Section3.T15.PlacementData
      u p f K) :
    placementOfContract (placementToContract place) = place := rfl

theorem localPotentialOfContract {v U : SpaceTimeField} {K : Set Space}
    {x₀ : Space} {r T δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.LocalPotentialAPI v U K x₀ r T δ D) :
    NSFormalization.Section3.T16.LocalPotentialAPI
      v U K x₀ r T δ (CutoffData.ofContract D) :=
  { theta_smooth := h.theta_smooth
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
    correction_cancels := h.correction_cancels }

theorem localizationOfContract (h : Contracts.V1.LocalizationAPI) :
    NSFormalization.Section3.T13.LocalizationAPI :=
  { constant_pos_finite := h.constant_pos_finite
    wholeSpace_identity := h.wholeSpace_identity
    torus_identity := h.torus_identity
    localization := h.localization
    endpoint_zero := h.endpoint_zero
    endpoint_one := h.endpoint_one }

theorem localizationToContract (h : NSFormalization.Section3.T13.LocalizationAPI) :
    Contracts.V1.LocalizationAPI :=
  { constant_pos_finite := h.constant_pos_finite
    wholeSpace_identity := h.wholeSpace_identity
    torus_identity := h.torus_identity
    localization := h.localization
    endpoint_zero := h.endpoint_zero
    endpoint_one := h.endpoint_one }


/-! Every restated non-record definition is checked by `rfl`. -/
theorem IsPeriodicLebesgueSlicePath_eq : @Contracts.V1.Correction3.IsPeriodicLebesgueSlicePath = @NSFormalization.Section3.T15.IsPeriodicLebesgueSlicePath := rfl
theorem mixedLebesgueENormT_eq : @Contracts.V1.Correction3.mixedLebesgueENormT = @NSFormalization.Section3.T15.mixedLebesgueENormT := rfl
theorem MemForceSobolevT_eq : @Contracts.V1.Correction3.MemForceSobolevT = @NSFormalization.Section3.T15.MemForceSobolevT := rfl
theorem alphaT_eq : @Contracts.V1.Correction3.alphaT = @NSFormalization.Section3.T15.alphaT := rfl
theorem rescaledPotential_eq : @Contracts.V1.Correction3.rescaledPotential = @NSFormalization.Section3.T17.rescaledPotential := rfl
theorem rescaledReference_eq : @Contracts.V1.Correction3.rescaledReference = @NSFormalization.Section3.T17.rescaledReference := rfl
theorem correctionChartPoint_eq : @Contracts.V1.Correction3.correctionChartPoint = @NSFormalization.Section3.T17.correctionChartPoint := rfl
theorem torusSpaceTimeLift_eq : @Contracts.V1.Correction3.torusSpaceTimeLift = @NSFormalization.Section3.T17.torusSpaceTimeLift := rfl
theorem torusSpatialSupport_eq : @Contracts.V1.Correction3.torusSpatialSupport = @NSFormalization.Section3.T17.torusSpatialSupport := rfl
theorem torusTemporalSupport_eq : @Contracts.V1.Correction3.torusTemporalSupport = @NSFormalization.Section3.T17.torusTemporalSupport := rfl
theorem fixedProfileCylinder_eq (D : Contracts.V1.CutoffData) :
    Contracts.V1.Correction3.fixedProfileCylinder D =
      NSFormalization.Section3.T17.fixedProfileCylinder (CutoffData.ofContract D) := rfl
theorem rescaledCorrectionProfile_eq (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) (D : Contracts.V1.CutoffData) :
    Contracts.V1.Correction3.rescaledCorrectionProfile v x₀ T ε D =
      NSFormalization.Section3.T17.rescaledCorrectionProfile v x₀ T ε (CutoffData.ofContract D) := rfl
theorem rescaledForceProfile_eq (ν : ℝ) (v : SpaceTimeField) (x₀ : Space) (T ε : ℝ) (D : Contracts.V1.CutoffData) :
    Contracts.V1.Correction3.rescaledForceProfile ν v x₀ T ε D =
      NSFormalization.Section3.T17.rescaledForceProfile ν v x₀ T ε (CutoffData.ofContract D) := rfl
theorem correctionForce_eq (ν : ℝ) (v : SpaceTimeField) (D : Contracts.V1.CutoffData) (ε : ℝ) :
    Contracts.V1.Correction3.correctionForce ν v D ε =
      NSFormalization.Section3.T17.correctionForce ν v (CutoffData.ofContract D) ε := rfl

def ofContract {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    {place : Contracts.V1.Correction3.PlacementData u p f K}
    {v : SpaceTimeField} {r δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.Correction3.CorrectionAPI ν place v r δ D) :
    NSFormalization.Section3.T17.CorrectionAPI ν (placementOfContract place) v r δ (CutoffData.ofContract D) :=
  { potential := localPotentialOfContract h.potential
    localization := localizationOfContract h.localization
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
    force_sobolev_bound := h.force_sobolev_bound }

def toContract {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    {place : NSFormalization.Section3.T15.PlacementData u p f K}
    {v : SpaceTimeField} {r δ : ℝ} {D : NSFormalization.Section3.T16.CutoffData}
    (h : NSFormalization.Section3.T17.CorrectionAPI ν place v r δ D) :
    Contracts.V1.Correction3.CorrectionAPI ν (placementToContract place) v r δ (CutoffData.toContract D) :=
  { potential := api_toContract h.potential
    localization := localizationToContract h.localization
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
    force_sobolev_bound := h.force_sobolev_bound }

theorem to_of {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    {place : Contracts.V1.Correction3.PlacementData u p f K} {v : SpaceTimeField} {r δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.Correction3.CorrectionAPI ν place v r δ D) :
    toContract (ofContract h) = h := by cases h; rfl

theorem of_to {ν : ℝ} {u : VelocityField} {p : PressureField}
    {f : VelocityField} {K : Set Space}
    {place : NSFormalization.Section3.T15.PlacementData u p f K} {v : SpaceTimeField} {r δ : ℝ} {D : NSFormalization.Section3.T16.CutoffData}
    (h : NSFormalization.Section3.T17.CorrectionAPI ν place v r δ D) :
    ofContract (toContract h) = h := by cases h; rfl

/-- The registered theorem has exactly the completed raw-field G4 block. -/
theorem correctionStatementAmended_holds : Contracts.V1.Correction3.correctionStatementAmended := by
  intro ν u p f K place v r δ hν hr hr2 hδ hper hv hdiv hsupp hball
  obtain ⟨D, hD, ⟨A⟩⟩ := NSFormalization.Section3.T17.correctionStatementAmended_holds
    ν u p f K (placementOfContract place) v r δ hν hr hr2 hδ hper hv hdiv hsupp hball
  exact ⟨CutoffData.toContract D, api_toContract hD, ⟨toContract A⟩⟩

/-! Packet-indexed Spec adapters and definitional bridges. -/
theorem Packet.fixedProfileCylinder_eq (D : Contracts.V1.CutoffData) :
    Contracts.V1.Correction3.Packet.fixedProfileCylinder D =
      NSFormalization.Section3.T17.fixedProfileCylinder (CutoffData.ofContract D) := rfl

theorem Packet.correctionChartPoint_eq {ν : ℝ} {P : PacketAPI ν}
    (place : Contracts.V1.Correction3.Packet.PlacementData P) (ε : ℝ) (z : SpaceTime) :
    Contracts.V1.Correction3.Packet.correctionChartPoint place ε z =
      NSFormalization.Section3.T17.correctionChartPoint
        (placementOfContract place).x₀ (placementOfContract place).T ε z := rfl

theorem Packet.rescaledReference_eq {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : Contracts.V1.Correction3.Packet.PlacementData P) (ε : ℝ) :
    Contracts.V1.Correction3.Packet.rescaledReference v place ε =
      NSFormalization.Section3.T17.rescaledReference
        v (placementOfContract place).x₀ (placementOfContract place).T ε := rfl

theorem Packet.rescaledPotential_eq {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : Contracts.V1.Correction3.Packet.PlacementData P) (ε : ℝ) :
    Contracts.V1.Correction3.Packet.rescaledPotential v place ε =
      NSFormalization.Section3.T17.rescaledPotential
        v (placementOfContract place).x₀ (placementOfContract place).T ε := rfl

theorem Packet.rescaledCorrectionProfile_eq {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : Contracts.V1.Correction3.Packet.PlacementData P)
    (ε : ℝ) (D : Contracts.V1.CutoffData) :
    Contracts.V1.Correction3.Packet.rescaledCorrectionProfile v place ε D =
      NSFormalization.Section3.T17.rescaledCorrectionProfile
        v (placementOfContract place).x₀ (placementOfContract place).T ε (CutoffData.ofContract D) := rfl

theorem Packet.rescaledForceProfile_eq {ν : ℝ} {P : PacketAPI ν}
    (v : SpaceTimeField) (place : Contracts.V1.Correction3.Packet.PlacementData P)
    (ε : ℝ) (D : Contracts.V1.CutoffData) :
    Contracts.V1.Correction3.Packet.rescaledForceProfile ν v place ε D =
      NSFormalization.Section3.T17.rescaledForceProfile
        ν v (placementOfContract place).x₀ (placementOfContract place).T ε (CutoffData.ofContract D) := rfl

theorem Packet.correctionForce_eq (ν : ℝ) (v : SpaceTimeField)
    (D : Contracts.V1.CutoffData) (ε : ℝ) :
    Contracts.V1.Correction3.Packet.correctionForce ν v D ε =
      NSFormalization.Section3.T17.correctionForce ν v (CutoffData.ofContract D) ε := rfl

theorem Packet.torusSpaceTimeLift_eq (f : SpaceTimeField) :
    Contracts.V1.Correction3.Packet.torusSpaceTimeLift f = NSFormalization.Section3.T17.torusSpaceTimeLift f := rfl

theorem Packet.torusSpatialSupport_eq (f : SpaceTimeField) :
    Contracts.V1.Correction3.Packet.torusSpatialSupport f = NSFormalization.Section3.T17.torusSpatialSupport f := rfl

theorem Packet.torusTemporalSupport_eq (f : SpaceTimeField) :
    Contracts.V1.Correction3.Packet.torusTemporalSupport f = NSFormalization.Section3.T17.torusTemporalSupport f := rfl


def ofPacket {ν : ℝ} {P : PacketAPI ν}
    {place : Contracts.V1.Correction3.Packet.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.Correction3.Packet.CorrectionAPI ν place v r δ D) :
    Contracts.V1.Correction3.CorrectionAPI ν place v r δ D :=
  { potential := h.potential
    localization := h.localization
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
    force_sobolev_bound := h.force_sobolev_bound }

def toPacket {ν : ℝ} {P : PacketAPI ν}
    {place : Contracts.V1.Correction3.Packet.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.Correction3.CorrectionAPI ν place v r δ D) :
    Contracts.V1.Correction3.Packet.CorrectionAPI ν place v r δ D :=
  { potential := h.potential
    localization := h.localization
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
    force_sobolev_bound := h.force_sobolev_bound }

theorem toPacket_ofPacket {ν : ℝ} {P : PacketAPI ν}
    {place : Contracts.V1.Correction3.Packet.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.Correction3.Packet.CorrectionAPI ν place v r δ D) :
    toPacket (ofPacket h) = h := by cases h; rfl

theorem ofPacket_toPacket {ν : ℝ} {P : PacketAPI ν}
    {place : Contracts.V1.Correction3.Packet.PlacementData P}
    {v : SpaceTimeField} {r δ : ℝ} {D : Contracts.V1.CutoffData}
    (h : Contracts.V1.Correction3.CorrectionAPI ν place v r δ D) :
    ofPacket (toPacket h) = h := by cases h; rfl

/-- Transport of the cube-centred nonzero witness through the registered records. -/
theorem nonvacuous_correction :
    NSFormalization.Section3.T17.Nonvacuity.reference ≠ 0 ∧
    ∃ D : Contracts.V1.CutoffData, 0 < D.ε₀ ∧ D.ε₀ ∈ Ioc (0 : ℝ) D.ε₀ ∧
      Nonempty (Contracts.V1.Correction3.CorrectionAPI 1
        (placementToContract NSFormalization.Section3.T17.Nonvacuity.place)
        NSFormalization.Section3.T17.Nonvacuity.reference (1 / 4) 1 D) := by
  obtain ⟨hne, D, hpos, hscale, _, ⟨A⟩⟩ :=
    NSFormalization.Section3.T17.Nonvacuity.nonvacuous_correction
  exact ⟨hne, CutoffData.toContract D, hpos, hscale, ⟨toContract A⟩⟩


/-! Statements mentioning distinct record types are transported fieldwise. -/
theorem correctionStatement_iff : Contracts.V1.Correction3.correctionStatement ↔
    NSFormalization.Section3.T17.correctionStatement := by
  constructor
  · intro h ν u p f K place v r δ
    obtain ⟨D, hD, ⟨A⟩⟩ := h ν u p f K (placementToContract place) v r δ
    exact ⟨CutoffData.ofContract D, localPotentialOfContract hD, ⟨ofContract A⟩⟩
  · intro h ν u p f K place v r δ
    obtain ⟨D, hD, ⟨A⟩⟩ := h ν u p f K (placementOfContract place) v r δ
    exact ⟨CutoffData.toContract D, api_toContract hD, ⟨toContract A⟩⟩

theorem correctionStatementAmended_iff : Contracts.V1.Correction3.correctionStatementAmended ↔
    NSFormalization.Section3.T17.correctionStatementAmended := by
  constructor
  · intro h ν u p f K place v r δ hν hr hr2 hδ hper hv hdiv hsupp hball
    obtain ⟨D, hD, ⟨A⟩⟩ := h ν u p f K (placementToContract place) v r δ
      hν hr hr2 hδ hper hv hdiv hsupp hball
    exact ⟨CutoffData.ofContract D, localPotentialOfContract hD, ⟨ofContract A⟩⟩
  · intro h ν u p f K place v r δ hν hr hr2 hδ hper hv hdiv hsupp hball
    obtain ⟨D, hD, ⟨A⟩⟩ := h ν u p f K (placementOfContract place) v r δ
      hν hr hr2 hδ hper hv hdiv hsupp hball
    exact ⟨CutoffData.toContract D, api_toContract hD, ⟨toContract A⟩⟩

theorem Packet.placementData_eq {ν : ℝ} (P : PacketAPI ν) :
    Contracts.V1.Correction3.Packet.PlacementData P =
      Contracts.V1.Correction3.PlacementData P.velocity P.pressure P.force P.carrier := rfl

theorem Packet.correctionStatement_iff : Contracts.V1.Correction3.Packet.correctionStatement ↔
    ∀ (ν : ℝ) {P : PacketAPI ν}
      (place : NSFormalization.Section3.T15.PlacementData
        P.velocity P.pressure P.force P.carrier)
      (v : SpaceTimeField) (r δ : ℝ),
      ∃ D : NSFormalization.Section3.T16.CutoffData,
        NSFormalization.Section3.T16.LocalPotentialAPI
          v P.velocity place.Kstar place.x₀ r place.T δ D ∧
        Nonempty (NSFormalization.Section3.T17.CorrectionAPI ν place v r δ D) := by
  constructor
  · intro h ν P place v r δ
    obtain ⟨D, hD, ⟨A⟩⟩ := h ν (placementToContract place) v r δ
    exact ⟨CutoffData.ofContract D, localPotentialOfContract hD, ⟨ofContract (ofPacket A)⟩⟩
  · intro h ν P place v r δ
    obtain ⟨D, hD, ⟨A⟩⟩ := h ν (placementOfContract place) v r δ
    exact ⟨CutoffData.toContract D, api_toContract hD, ⟨toPacket (toContract A)⟩⟩

end BlowupDensity.Bindings.Correction3
