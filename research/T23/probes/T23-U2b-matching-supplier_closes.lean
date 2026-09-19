import NSFormalization.Section3.T23.CorrectionEstimates
import Bindings.CorrectionV2
import Bindings.Scaling

/-! Registered I02/I03 consumption; no whole-space supplier is assumed. -/
noncomputable section
namespace T23U2b
open BlowupDensity.Contracts.V1
open Set MeasureTheory
open NSFormalization.Section3.T23
open scoped ContDiff ENNReal

def correctionTo {ν : ℝ} {P : PacketAPI ν} (b : CorrectionAPI ν P) : NSFormalization.Section3.T23.WholeSpaceCorrectionAPI ν P.velocity P.carrier where
  T := b.T
  time_pos := b.time_pos
  δ := b.δ
  margin_pos := b.margin_pos
  v := b.v
  π := b.π
  g := b.g
  reference_smooth := b.reference_smooth
  reference_pressure_smooth := b.reference_pressure_smooth
  reference_divergence_free := b.reference_divergence_free
  reference_equation := b.reference_equation
  x₀ := b.x₀
  r := b.r
  radius_pos := b.radius_pos
  θ := b.θ
  theta_smooth := b.theta_smooth
  theta_compactSupport := b.theta_compactSupport
  plateau := b.plateau
  plateau_open := b.plateau_open
  carrier_subset_plateau := b.carrier_subset_plateau
  theta_one := b.theta_one
  θRadius := b.θRadius
  theta_radius_pos := b.theta_radius_pos
  theta_support := b.theta_support
  η := b.η
  eta_smooth := b.eta_smooth
  eta_compactSupport := b.eta_compactSupport
  eta_one := b.eta_one
  eta_support := b.eta_support
  ε₀ := b.ε₀
  eps_pos := b.eps_pos
  eps_le_one := b.eps_le_one
  eps_time := b.eps_time
  eps_space := b.eps_space
  potential := b.potential
  potential_smooth := b.potential_smooth
  potential_formula := b.potential_formula
  potential_curl := b.potential_curl
  correction := b.correction
  correction_formula := b.correction_formula
  correction_smooth := b.correction_smooth
  correction_divergence_free := b.correction_divergence_free
  correction_compactSupport := b.correction_compactSupport
  correction_support := b.correction_support
  correction_support_ball := b.correction_support_ball
  correction_vanishes_before := b.correction_vanishes_before
  correction_cancels := b.correction_cancels
  correction_cancels_germ := b.correction_cancels_germ
  correctionDerivConst := b.correctionDerivConst
  correctionDerivConst_nonneg := b.correctionDerivConst_nonneg
  correction_derivative_bound := b.correction_derivative_bound
  forceCorrection := b.forceCorrection
  force_formula := b.force_formula
  force_smooth := b.force_smooth
  force_compactSupport := b.force_compactSupport
  force_support := b.force_support
  force_positive_time := b.force_positive_time
  force_support_ball := b.force_support_ball
  spatialVolumeConst := b.spatialVolumeConst
  force_spatial_volume := b.force_spatial_volume
  force_time_length := b.force_time_length
  forceDerivConst := b.forceDerivConst
  forceDerivConst_nonneg := b.forceDerivConst_nonneg
  force_derivative_bound := b.force_derivative_bound
  energyConst := b.energyConst
  correction_slice_memLp := b.correction_slice_memLp
  correction_gradient_memLp := b.correction_gradient_memLp
  correction_energy_bound := b.correction_energy_bound
  mixedConst := b.mixedConst
  force_spatial_memLp := b.force_spatial_memLp
  force_mixed_bound := b.force_mixed_bound
  corrected_background := b.corrected_background
  perturbation_divergence_free := b.perturbation_divergence_free

/-- Construct the registered pair from the local reference, retaining exactly
I03's same-C equation and the local correction/force identities. -/
theorem exists_matching_supplier {ν T δ r : ℝ} (P : PacketAPI ν)
    (th : ThresholdAPI) (v : VelocityField) (x₀ : Space)
    (hT : 0 < T) (hδ : 0 < δ) (hr : 0 < r)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ (C : CorrectionAPI ν P) (A : ScalingAPI ν P) (D : CutoffData),
      A.correction = C ∧ C.T = T ∧ C.δ = δ ∧ C.x₀ = x₀ ∧
      C.r = r / 2 ∧ A.thresholds = th ∧
      0 < D.ε₀ ∧ D.ε₀ ≤ A.ε₀ ∧
      D = localCorrectionData v x₀ T C.θ C.η C.plateau C.θRadius A.ε₀ ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        D.correction ε = C.correction ε ∧
        NSFormalization.Section3.T23.correctionForce ν v D ε = C.forceCorrection ε) := by
  obtain ⟨V, hV, hdV, heqV⟩ := exists_spatial_solenoidal_extension isOpen_Ioo hr hv hdiv
  let C₂ := BlowupDensity.Bindings.correctionV2 P x₀ P.carrier_compact hT hδ
    (half_pos hr) hV ((contDiff_const (c := (0 : ℝ))).contDiffOn) hdV
    (g := fun z => navierStokesResidual ν V (fun _ => 0) z.1 z.2)
    (fun _ _ _ => rfl)
  let C := C₂.toCorrectionAPI
  let A := BlowupDensity.Bindings.scaling C th
  let D := localCorrectionData v x₀ T C.θ C.η C.plateau C.θRadius A.ε₀
  refine ⟨C, A, D, rfl, rfl, rfl, rfl, rfl, rfl, A.eps_pos, le_rfl, rfl, ?_⟩
  intro ε hε
  apply (correctionTo C).local_match (e := A.ε₀) ?_ ⟨hε.1,
    hε.2.trans A.eps_le_correction⟩
  exact fun z hz => (heqV hz).symm

end T23U2b
