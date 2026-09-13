import NavierStokes.ActualInitialization
import NavierStokes.ActualCarrierGeometry

/-!
# Closure of the actual base-profile choice

The primary family and initialization already use one closed profile selected
by `FinalSlowBase.profileData_nonempty`.  These bindings expose its retained
parameter bounds, common pressure datum, cone certificate, and the initialized
state at budget zero and the actual geometric starting threshold.

There is no outgoing-profile, nominal-profile, cone, or modulation hypothesis
in any declaration below.  The threshold choices are the existing proved
choices; this module does not select an independent base.
-/

namespace NavierStokes.BaseWitnessClosure

open CorrectionInitialization

/-- The initialization's base is literally the closed final slow-base choice. -/
theorem actual_profile_eq : ActualPrimary.profile = FinalSlowBase.actualProfile := rfl

/-- Bounds retained by the actual outgoing schedule, without recovering
additional properties from the implementation of `Classical.choice`. -/
theorem actual_outgoing_parameters :
    0 < ActualPrimary.outgoing.data.core.P ∧
      0 < ActualPrimary.outgoing.data.core.m ∧
      0 < ActualPrimary.outgoing.data.core.lam ∧
      ActualPrimary.outgoing.data.core.lam < 1 / 10 ∧
      25 < ActualPrimary.outgoing.data.core.wait :=
  ⟨ActualPrimary.outgoing.data.core.P_pos,
    ActualPrimary.outgoing.data.core.m_pos,
    ActualPrimary.outgoing.data.core.lam_pos,
    ActualPrimary.outgoing.data.core.lam_lt,
    ActualPrimary.outgoing.data.core.wait_gt⟩

/-- The height and nonzero axial seed belong to the same retained axis stage. -/
theorem actual_axis_parameters :
    0 < ActualPrimary.h ∧ ActualPrimary.h ≤ 1 / 1000 ∧
      2 * ActualPrimary.h < ActualPrimary.outgoing.data.core.lam ∧
      0 < ActualPrimary.nominal.axis.j ∧ ActualPrimary.nominal.axis.j ≤ 1 / 1000 :=
  ⟨ActualPrimary.nominal.axis.small.h_pos,
    ActualPrimary.nominal.axis.small.h_le,
    ActualPrimary.outgoing.data.h_small,
    ActualPrimary.nominal.axis.small.j_pos,
    ActualPrimary.nominal.axis.small.j_le⟩

/-- The natural scale and normalization satisfy their actual preceding
thresholds, including the normalization's dependence on the selected scale. -/
theorem actual_scale_order :
    0 < ActualPrimary.nominal.axis.scale ∧
      ActualPrimary.nominal.axis.preparation.scaleBound ≤ ActualPrimary.nominal.axis.scale ∧
      0 < ActualPrimary.nominal.axis.normalization ∧
      NaturalEntrance.entranceNormalization ActualPrimary.nominal.axis.preparation.inputs
          ActualPrimary.nominal.axis.scale ActualPrimary.nominal.axis.preparation.delta ≤
        ActualPrimary.nominal.axis.normalization :=
  ⟨ActualPrimary.nominal.axis.scale_pos,
    ActualPrimary.nominal.axis.scale_large,
    ActualPrimary.nominal.axis.normalization_pos,
    ActualPrimary.nominal.axis.normalization_large⟩

/-- Both certificates concern the actual profile used by the primary fields,
and modulation preserves its original outgoing axis pressure. -/
theorem actual_base_compatible :
    OutgoingProfile.Specification ActualPrimary.outgoing ActualPrimary.nominal.outgoingBound ∧
      NominalConeAssembly.Certificate ActualPrimary.nominal ∧
      LeadingStressWeights.FullTrueCone ActualPrimary.modulation ∧
      ActualPrimary.modulation.profiles.pressure0 = ActualPrimary.outgoing.axisDatum :=
  ⟨ActualPrimary.nominal.outgoing_specification,
    ActualPrimary.certificate,
    ActualPrimary.profile.fullTrueCone,
    ActualPrimary.modulation.same_axis_pressure⟩

/-- The fixed box strictly contains the same positive, nonempty active annulus. -/
theorem actual_annulus_order :
    0 < NominalConeAssembly.activeLeft ActualPrimary.nominal ∧
      NominalConeAssembly.activeLeft ActualPrimary.nominal <
        NominalConeAssembly.activeRight ActualPrimary.nominal ∧
      NominalConeAssembly.activeRight ActualPrimary.nominal < ActualPrimary.upper := by
  refine ⟨NominalConeAssembly.activeLeft_pos ActualPrimary.nominal,
    PrimaryGeometryAssembly.active_order (W := ActualPrimary.nominal), ?_⟩
  change NominalConeAssembly.activeRight ActualPrimary.nominal <
    2 * NominalConeAssembly.activeRight ActualPrimary.nominal
  linarith [FinalSlowBase.terminal_pos ActualPrimary.nominal]

/-- Smooth coefficients and finite slow identities are consequences of the
same certificate and modulation, rather than additional base assumptions. -/
theorem actual_finite_base :
    SlowBorelBase.SmoothCoefficients
        (FinalSlowBase.coefficients ActualPrimary.certificate ActualPrimary.modulation) ∧
      BaseResidual.FiniteIdentities ActualPrimary.h ActualPrimary.nominal.axis.normalization
        (FinalSlowBase.coefficients ActualPrimary.certificate ActualPrimary.modulation)
        (FinalSlowBase.profileSequence ActualPrimary.certificate ActualPrimary.modulation) :=
  ⟨FinalSlowBase.coefficients_smooth ActualPrimary.certificate ActualPrimary.modulation,
    FinalSlowBase.finiteIdentities ActualPrimary.certificate ActualPrimary.modulation⟩

/-- At budget zero the prepared primary threshold exceeds the actual geometric
floor selected before the primary family. -/
theorem selected_threshold_order :
    ActualCarrierGeometry.geometricThreshold ≤ ActualCarrierGeometry.startingThreshold 0 ∧
      ActualCarrierGeometry.startingThreshold 0 ≤
        (ActualPrimary.choice 0 (ActualCarrierGeometry.startingThreshold 0)).prepared.N :=
  ⟨ActualCarrierGeometry.geometricThreshold_le_startingThreshold 0,
    ActualCarrierGeometry.startingThreshold_le_prepared 0 0⟩

/-- This is the initialization and exact budget/threshold pair used by the
final construction.  In particular, no base-certificate premise remains. -/
theorem selected_initial_invariant :
    CorrectionStep.CycleAnalyticInvariant ActualInitialization.geometry
      (ActualPrimary.commonContext 0)
      (ActualInitialization.tangentBlock
        (B := 0) (N0 := ActualCarrierGeometry.startingThreshold 0))
      ActualInitialization.envelope ActualInitialization.labelCarrier (1 / 5)
      (ActualInitialization.initialCycleState 0 (ActualCarrierGeometry.startingThreshold 0)) :=
  ActualInitialization.initial_invariant 0 (ActualCarrierGeometry.startingThreshold 0)

/-- An explicit closed existential form, useful when a consumer asks for a
starting pair rather than the named choices.  The output invariant is proved
by the actual initialization theorem, with every field retained. -/
theorem exists_closed_initialization :
    ∃ B N0 : ℕ, B = 0 ∧ N0 = ActualCarrierGeometry.startingThreshold 0 ∧
      ActualCarrierGeometry.geometricThreshold ≤ N0 ∧
      N0 ≤ (ActualPrimary.choice B N0).prepared.N ∧
      CorrectionStep.CycleAnalyticInvariant ActualInitialization.geometry
        (ActualPrimary.commonContext B)
        (ActualInitialization.tangentBlock (B := B) (N0 := N0))
        ActualInitialization.envelope ActualInitialization.labelCarrier (1 / 5)
        (ActualInitialization.initialCycleState B N0) :=
  ⟨0, ActualCarrierGeometry.startingThreshold 0, rfl, rfl,
    selected_threshold_order.1, selected_threshold_order.2, selected_initial_invariant⟩

end NavierStokes.BaseWitnessClosure
