import NSFormalization.Section3.T23.Assembly
import NSFormalization.Section3.T23.CorrectionEstimates
import Bindings.CorrectionV2
import Bindings.Scaling
import Contracts.V1.BoundaryInsertion
import Bindings.Thresholds

/-! Registered I02/I03 suppliers, the 48-field T23 construction, and fieldwise
contract conversions. The smooth branch retains explicit scalar IBP. -/
noncomputable section
namespace BlowupDensity.Bindings.BoundaryInsertion
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
theorem exists_matching_supplier {ν T δ r ρ : ℝ} (P : PacketAPI ν)
    (th : ThresholdAPI) (v : VelocityField) (x₀ : Space)
    (hT : 0 < T) (hδ : 0 < δ) (_hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < r)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ (C : CorrectionAPI ν P) (A : ScalingAPI ν P) (D : CutoffData),
      A.correction = C ∧ C.T = T ∧ C.δ = δ ∧ C.x₀ = x₀ ∧
      C.r = ρ ∧ A.thresholds = th ∧
      0 < D.ε₀ ∧ D.ε₀ ≤ A.ε₀ ∧ D.ε₀ = C.ε₀ ∧
      EqOn v C.v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ (ρ)) ∧
      D = localCorrectionData v x₀ T C.θ C.η C.plateau C.θRadius A.ε₀ ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        D.correction ε = C.correction ε ∧
        NSFormalization.Section3.T23.correctionForce ν v D ε = C.forceCorrection ε) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        Data.energyENorm T (D.correction ε) ≤ ENNReal.ofReal (B * ε ^ ((3 : ℝ) / 2))) ∧
      (∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], ∃ B : ℝ, 0 < B ∧
        ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          Data.mixedLebesgueENorm q p (NSFormalization.Section3.T23.correctionForce ν v D ε) ≤
            ENNReal.ofReal (B * ε ^ (alpha p q + 1))) ∧
      (∀ q : ℝ≥0∞, 1 ≤ q → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ∃ B : ℝ, 0 < B ∧ ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          Data.forceSobolevENorm q s (NSFormalization.Section3.T23.correctionForce ν v D ε) ≤
            ENNReal.ofReal (B *
              (ε ^ (2 / q.toReal - 1 / 2) + ε ^ (2 / q.toReal - 1 / 2 - s)))) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
        spatialDerivative (scaledPacket P.velocity x₀ T ε) t x
          (v (t, x) + D.correction ε (t, x)) = 0 ∧
        spatialDerivative (fun z => v z + D.correction ε z) t x
          (scaledPacket P.velocity x₀ T ε (t, x)) = 0) := by
  obtain ⟨V, hV, hdV, heqV⟩ := exists_spatial_solenoidal_extension_between isOpen_Ioo hρ hρr hv hdiv
  let C₂ := BlowupDensity.Bindings.correctionV2 P x₀ P.carrier_compact hT hδ
    hρ hV ((contDiff_const (c := (0 : ℝ))).contDiffOn) hdV
    (g := fun z => navierStokesResidual ν V (fun _ => 0) z.1 z.2)
    (fun _ _ _ => rfl)
  let C := C₂.toCorrectionAPI
  let A := BlowupDensity.Bindings.scaling C th
  let D := localCorrectionData v x₀ T C.θ C.η C.plateau C.θRadius A.ε₀
  have heA : A.ε₀ = C.ε₀ := by
    change min C.ε₀ (Real.sqrt (min T δ / 4 / 2)) = C.ε₀
    apply min_eq_left
    change min 1 (min _ (Real.sqrt (min T δ / 4 / 2))) ≤ _
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hmatch : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      D.correction ε = C.correction ε ∧
        NSFormalization.Section3.T23.correctionForce ν v D ε = C.forceCorrection ε := by
    intro ε hε
    exact (correctionTo C).local_match (e := A.ε₀)
      (fun z hz => (heqV hz).symm) ⟨hε.1, hε.2.trans A.eps_le_correction⟩
  refine ⟨C, A, D, rfl, rfl, rfl, rfl, rfl, rfl, A.eps_pos, le_rfl, heA, (fun z hz => (heqV hz).symm), rfl,
    hmatch, ?_, ?_, ?_, ?_⟩
  · refine ⟨A.correctionEnergyConst, A.correctionEnergyConst_nonneg, ?_⟩
    intro ε hε
    rw [(hmatch ε hε).1]
    exact A.correctionEnergyBound ε hε
  · exact (correctionTo C).local_mixed_bound (fun z hz => (heqV hz).symm)
      A.eps_le_correction
  · intro q hq s hs hs1
    let b := A.correctionPositiveConst q s
    refine ⟨max b 0 + 1, by positivity, ?_⟩
    intro ε hε
    rw [(hmatch ε hε).2]
    have hb := A.correctionPositiveScaling q hq s hs hs1 ε hε
    have hx (s : ℝ) : th.exponent q.toReal s + 1 = 2 / q.toReal - 1 / 2 - s := by
      rw [th.formula]; ring
    change Data.forceSobolevENorm q s (C.forceCorrection ε) ≤
      ENNReal.ofReal (b * (ε ^ (th.exponent q.toReal 0 + 1) +
        ε ^ (th.exponent q.toReal s + 1))) at hb
    rw [hx 0, hx s, sub_zero] at hb
    apply hb.trans
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_right ((le_max_left b 0).trans (by linarith))
    exact add_nonneg (Real.rpow_nonneg hε.1.le _) (Real.rpow_nonneg hε.1.le _)
  · have hball : Metric.ball x₀ (ρ) ⊆ Metric.ball x₀ r :=
      Metric.ball_subset_ball (by linarith)
    exact (correctionTo C).local_crossTransport P.carrier_compact
      (hv.mono (Set.prod_mono Subset.rfl hball))
      (fun t ht x hx => hdiv t ht x (hball hx)) (fun t ht => P.velocity_support t ⟨ht.1.le, ht.2⟩) A.eps_le_correction

/-- The cutoff spelling in G0: copy the supplier potential and family literally,
while proving the force identity for the original domain-local reference. -/
theorem exists_matching_registered_cutoff {ν T δ r ρ : ℝ} (P : PacketAPI ν)
    (th : ThresholdAPI) (v : VelocityField) (x₀ : Space)
    (hT : 0 < T) (hδ : 0 < δ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < r)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0) :
    ∃ (C : CorrectionAPI ν P) (A : ScalingAPI ν P) (D : CutoffData),
      A.correction = C ∧ C.T = T ∧ C.δ = δ ∧ C.x₀ = x₀ ∧ C.r = ρ ∧
      EqOn C.v v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ (ρ)) ∧
      D.θ = C.θ ∧ D.η = C.η ∧ D.plateau = C.plateau ∧
      D.θRadius = C.θRadius ∧ D.ε₀ = C.ε₀ ∧ D.ε₀ ≤ A.ε₀ ∧ 0 < D.ε₀ ∧
      D.potential = C.potential ∧ D.correction = C.correction ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        NSFormalization.Section3.T23.correctionForce ν v D ε = C.forceCorrection ε) ∧
      (∃ B : ℝ, 0 ≤ B ∧ ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        Data.energyENorm T (D.correction ε) ≤ ENNReal.ofReal (B * ε ^ ((3 : ℝ) / 2))) ∧
      (∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)], ∃ B : ℝ, 0 < B ∧
        ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          Data.mixedLebesgueENorm q p (NSFormalization.Section3.T23.correctionForce ν v D ε) ≤
            ENNReal.ofReal (B * ε ^ (alpha p q + 1))) ∧
      (∀ q : ℝ≥0∞, 1 ≤ q → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        ∃ B : ℝ, 0 < B ∧ ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
          Data.forceSobolevENorm q s (NSFormalization.Section3.T23.correctionForce ν v D ε) ≤
            ENNReal.ofReal (B *
              (ε ^ (2 / q.toReal - 1 / 2) + ε ^ (2 / q.toReal - 1 / 2 - s)))) ∧
      (∀ ε ∈ Ioc (0 : ℝ) D.ε₀, ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space,
        spatialDerivative (scaledPacket P.velocity x₀ T ε) t x
          (v (t, x) + D.correction ε (t, x)) = 0 ∧
        spatialDerivative (fun z => v z + D.correction ε z) t x
          (scaledPacket P.velocity x₀ T ε (t, x)) = 0) := by
  obtain ⟨C, A, L, hAC, hT', hδ', hx, hr', _, _, he, hcut, heq, _, hm, hE, hM, hS, hX⟩ :=
    exists_matching_supplier P th v x₀ hT hδ hr hρ hρr hv hdiv
  let D := (correctionTo C).supplierCutoff
  have hF : ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
      NSFormalization.Section3.T23.correctionForce ν v D ε = C.forceCorrection ε := by
    intro ε hε
    apply (correctionTo C).supplierCutoff_force ?_ hε
    simpa only [correctionTo, hT', hδ', hx, hr'] using heq
  have hεL {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) D.ε₀) : ε ∈ Ioc (0 : ℝ) L.ε₀ := by
    rw [hcut]
    exact hε
  refine ⟨C, A, D, hAC, hT', hδ', hx, hr', (fun z hz => (heq hz).symm),
    rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, hF, ?_, ?_, ?_, ?_⟩
  · change C.ε₀ ≤ A.ε₀
    rw [← hcut]
    exact he
  · exact C.eps_pos
  · obtain ⟨B, hB, hb⟩ := hE
    refine ⟨B, hB, ?_⟩
    intro ε hε
    change Data.energyENorm T (C.correction ε) ≤ _
    rw [← (hm ε (hεL hε)).1]
    exact hb ε (hεL hε)
  · intro p q _
    obtain ⟨B, hB, hb⟩ := hM p q
    refine ⟨B, hB, ?_⟩
    intro ε hε
    rw [hF ε hε, ← (hm ε (hεL hε)).2]
    exact hb ε (hεL hε)
  · intro q hq s hs hs1
    obtain ⟨B, hB, hb⟩ := hS q hq s hs hs1
    refine ⟨B, hB, ?_⟩
    intro ε hε
    rw [hF ε hε, ← (hm ε (hεL hε)).2]
    exact hb ε (hεL hε)
  · intro ε hε t ht x
    have h := hX ε (hεL hε) t ht x
    rw [(hm ε (hεL hε)).1] at h
    exact h

/-- The exact residual conjunction instantiated with an actual domain reference. -/
theorem exists_matching_supplier_on_domain {ν T δ r ρ : ℝ} (P : PacketAPI ν)
    (th : ThresholdAPI) (Ω : Set Space) (a : Data.SpatialField) (g : VelocityField)
    (reference : ClassicalSolutionOmega ν Ω a g (T + δ)) (x₀ : Space)
    (hT : 0 < T) (hδ : 0 < δ) (hr : 0 < r) (hρ : 0 < ρ) (hρr : ρ < r) (hball : Metric.ball x₀ r ⊆ Ω) :
    ∃ (C : CorrectionAPI ν P) (A : ScalingAPI ν P) (D : CutoffData),
      A.correction = C ∧ C.T = T ∧ C.δ = δ ∧ C.x₀ = x₀ ∧
      0 < D.ε₀ ∧ D.ε₀ ≤ A.ε₀ ∧
      ∀ ε ∈ Ioc (0 : ℝ) D.ε₀,
        D.correction ε = C.correction ε ∧
        NSFormalization.Section3.T23.correctionForce ν reference.velocity D ε =
          C.forceCorrection ε := by
  have hl := reference.local_velocity x₀ hball
  obtain ⟨C, A, D, hAC, hCT, hCδ, hx, _, _, hp, he, _, _, _, hm, _⟩ :=
    exists_matching_supplier P th reference.velocity x₀ hT hδ hr hρ hρr hl.1 hl.2
  exact ⟨C, A, D, hAC, hCT, hCδ, hx, hp, he, hm⟩

/-- All supplier hypotheses are discharged from the packet and the given
local domain reference. The smooth-domain branch exposes only the proved
uniqueness engine's scalar integration-by-parts premise. -/
theorem boundaryInsertionStatement'_of_ibp {ν : ℝ} (P : PacketAPI ν)
    (th : ThresholdAPI) (place : DomainPlacementData P.velocity P.pressure P.force P.carrier)
    (Ω : Set Space) (norms : NSFormalization.Section3.T22.BoundedDomainNormAPI)
    (a : Data.SpatialField) (g : VelocityField) (r δ : ℝ)
    (reference : ClassicalSolutionOmega ν Ω a g (place.T + δ))
    (hΩ : IsBoundedBoxOrSmoothDomain Ω) (hI : IBP Ω) (hδ : 0 < δ) (hr : 0 < r)
    (hg : g ∈ forceClassOmega Ω) (ha : a ∈ initialClassOmega Ω)
    (hrball : closure (Metric.ball place.x₀ r) ⊆ Metric.ball place.chartCenter place.chartRadius)
    (hball : closure (Metric.ball place.chartCenter place.chartRadius) ⊆ Ω) :
    ∃ (C : CorrectionAPI ν P) (D : CutoffData),
      C.T = place.T ∧ C.δ = δ ∧ C.x₀ = place.x₀ ∧ C.r = r ∧
      (∀ t ∈ Ioo (0 : ℝ) (place.T + δ), ∀ x ∈ Metric.ball place.x₀ r,
        C.v (t, x) = reference.velocity (t, x)) ∧
      D.θ = C.θ ∧ D.η = C.η ∧ D.plateau = C.plateau ∧
      D.θRadius = C.θRadius ∧ D.ε₀ = C.ε₀ ∧
      D.potential = C.potential ∧ D.correction = C.correction ∧
      Nonempty (BoundaryInsertionAPI ν P.velocity P.pressure P.force P.carrier
        P.energyBound P.dissipationBound place Ω norms a g r δ D reference) := by
  have hclosed : closure (Metric.ball place.x₀ r) ⊆ Ω :=
    hrball.trans (subset_closure.trans hball)
  obtain ⟨R, hR, hRball⟩ := exists_outer_ball hΩ.1 hr hclosed
  have hl := reference.local_velocity place.x₀ hRball
  obtain ⟨C, A, L, hAC, hCT, hCδ, hx, hCr, _, _, _, _, hmatch, _⟩ :=
    exists_matching_supplier P th reference.velocity place.x₀ place.time_pos hδ
      (hr.trans hR) hr hR hl.1 hl.2
  let c := correctionTo C
  let D := c.supplierCutoff
  have heq : EqOn reference.velocity c.v
      (Ioo (0 : ℝ) (c.T + c.δ) ×ˢ Metric.ball c.x₀ c.r) := by
    simpa only [c, correctionTo, hCT, hCδ, hx, hCr] using hmatch
  have hlocal := reference.local_velocity place.x₀ (subset_closure.trans hclosed)
  have hcore : WindowedCorrectionCore reference.velocity P.velocity P.carrier
      place.x₀ r place.T δ D := by
    have hc := c.windowedCore P.carrier_compact heq
      (by simpa only [c, correctionTo, hCT, hCδ, hx, hCr] using hlocal.1)
      (by simpa only [c, correctionTo, hCT, hCδ, hx, hCr] using hlocal.2)
      (fun t ht => P.velocity_support t ⟨ht.1.le, ht.2⟩)
    change WindowedCorrectionCore reference.velocity P.velocity P.carrier C.x₀ C.r C.T C.δ D at hc
    simpa only [hCT, hCδ, hx, hCr] using hc
  have hforce {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) C.ε₀) :
      NSFormalization.Section3.T23.correctionForce ν reference.velocity D ε = C.forceCorrection ε :=
    c.supplierCutoff_force heq hε
  let s := min C.ε₀ A.ε₀
  have hεA {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) s) : ε ∈ Ioc (0 : ℝ) A.ε₀ :=
    ⟨hε.1, hε.2.trans (min_le_right _ _)⟩
  have hεC {ε : ℝ} (hε : ε ∈ Ioc (0 : ℝ) s) : ε ∈ Ioc (0 : ℝ) C.ε₀ :=
    ⟨hε.1, hε.2.trans (min_le_left _ _)⟩
  have he (q : ℝ) : A.thresholds.exponent (1 : ℝ≥0∞).toReal q = 1 / 2 - q := by
    rw [A.thresholds.formula]; norm_num
  have he' (q : ℝ) : A.thresholds.exponent (1 : ℝ≥0∞).toReal q + 1 = 3 / 2 - q := by
    rw [he]; ring
  refine ⟨C, D, hCT, hCδ, hx, hCr, ?_, ?_⟩
  · intro t ht x hx'
    exact (@hmatch (t, x) ⟨ht, hx'⟩).symm
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  refine ⟨?_⟩
  apply boundaryInsertionAPI place norms D reference P.viscosity_pos hΩ hI hδ hg ha
    hball (subset_closure.trans hclosed) hcore C.eps_pos P.carrier_compact P.velocity_support
    P.force_smooth P.force_support P.velocity_extension_smooth P.pressure_extension_smooth
    P.speed_unbounded C.θRadius s P.energyBound P.dissipationBound A.correctionEnergyConst
    (lt_min C.eps_pos A.eps_pos)
    (by simpa only [hAC] using A.carrier_subset)
    (fun ε hε t ht x => BlowupDensity.Bindings.scaled_divergence_free P place.x₀ hε.1 ht x)
    (fun ε hε t ht x => BlowupDensity.Bindings.scaled_equation P place.x₀ hε.1 ht x)
    (fun ε hε => by
      have hb := A.perturbationEnergyBound ε (hεA hε)
      change NSFormalization.Section3.T24.energyENorm A.correction.T
        (fun z => A.correction.correction ε z + NSFormalization.Section3.T15.scaledVelocity
          P.velocity A.correction.x₀ A.correction.T ε z) ≤ _ at hb
      rw [hAC, hCT, hx] at hb
      exact hb)
    (A.positiveConst 1) (A.correctionPositiveConst 1)
  · intro q hq hq' ε hε
    have hb := A.packetPositiveScaling 1 le_rfl q hq (by linarith) ε (hεA hε)
    change NSFormalization.Section4.D01.forceSobolevENorm 1 q
      (NSFormalization.Section3.T15.scaledForce P.force A.correction.x₀ A.correction.T ε) ≤ _ at hb
    rw [hAC, hCT, hx, he, he, sub_zero] at hb
    exact hb
  · intro q hq hq' ε hε
    rw [hforce (hεC hε)]
    have hb := A.correctionPositiveScaling 1 le_rfl q hq (by linarith) ε (hεA hε)
    change NSFormalization.Section4.D01.forceSobolevENorm 1 q (A.correction.forceCorrection ε) ≤ _ at hb
    rw [hAC, he', he', sub_zero] at hb
    exact hb


end BlowupDensity.Bindings.BoundaryInsertion

namespace BlowupDensity.Bindings.BoundaryInsertion.Contract
open Set MeasureTheory Filter Topology
open BlowupDensity.Contracts.V1 BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.BoundaryInsertion BlowupDensity.Contracts.V1.BoundedDomainNorm
open scoped ContDiff ENNReal Topology
variable {ν : ℝ} {P : PacketImportAPI ν} {Ω : Set Space}
  {a : SpatialField} {g : SpaceTimeField} {T : ℝ}
def placeTo (b : DomainPlacementData P.toPacketAPI) : NSFormalization.Section3.T23.DomainPlacementData P.velocity P.pressure P.force P.carrier where
  T := b.T
  time_pos := b.time_pos
  chartCenter := b.chartCenter
  chartRadius := b.chartRadius
  chartRadius_pos := b.chartRadius_pos
  x₀ := b.x₀
  x₀_mem := b.x₀_mem
  Kstar := b.Kstar
  Kstar_compact := b.Kstar_compact
  carrier_subset := b.carrier_subset
  force_projection_subset := b.force_projection_subset
  ε₀ := b.ε₀
  eps_pos := b.eps_pos
  eps_le_one := b.eps_le_one
  eps_time := b.eps_time
  eps_space := b.eps_space

def placeFrom (b : NSFormalization.Section3.T23.DomainPlacementData P.velocity P.pressure P.force P.carrier) : DomainPlacementData P.toPacketAPI where
  T := b.T
  time_pos := b.time_pos
  chartCenter := b.chartCenter
  chartRadius := b.chartRadius
  chartRadius_pos := b.chartRadius_pos
  x₀ := b.x₀
  x₀_mem := b.x₀_mem
  Kstar := b.Kstar
  Kstar_compact := b.Kstar_compact
  carrier_subset := b.carrier_subset
  force_projection_subset := b.force_projection_subset
  ε₀ := b.ε₀
  eps_pos := b.eps_pos
  eps_le_one := b.eps_le_one
  eps_time := b.eps_time
  eps_space := b.eps_space

def cutoffTo (b : CutoffData) : NSFormalization.Section3.T23.CutoffData where
  θ := b.θ
  η := b.η
  plateau := b.plateau
  θRadius := b.θRadius
  ε₀ := b.ε₀
  potential := b.potential
  correction := b.correction

def cutoffFrom (b : NSFormalization.Section3.T23.CutoffData) : CutoffData where
  θ := b.θ
  η := b.η
  plateau := b.plateau
  θRadius := b.θRadius
  ε₀ := b.ε₀
  potential := b.potential
  correction := b.correction

def solutionTo (b : ClassicalSolutionOmega ν Ω a g T) : NSFormalization.Section3.T23.ClassicalSolutionOmega ν Ω a g T where
  velocity := b.velocity
  pressure := b.pressure
  horizon_pos := b.horizon_pos
  velocity_smooth := b.velocity_smooth
  pressure_smooth := b.pressure_smooth
  initial := b.initial
  divergence := b.divergence
  momentum := b.momentum
  no_slip := b.no_slip
  pressure_gauge := b.pressure_gauge

def solutionFrom (b : NSFormalization.Section3.T23.ClassicalSolutionOmega ν Ω a g T) : ClassicalSolutionOmega ν Ω a g T where
  velocity := b.velocity
  pressure := b.pressure
  horizon_pos := b.horizon_pos
  velocity_smooth := b.velocity_smooth
  pressure_smooth := b.pressure_smooth
  initial := b.initial
  divergence := b.divergence
  momentum := b.momentum
  no_slip := b.no_slip
  pressure_gauge := b.pressure_gauge

theorem normsTo (b : BoundedDomainNormAPI) : NSFormalization.Section3.T22.BoundedDomainNormAPI where
  orderZero := b.orderZero
  cutoffMultiplier := b.cutoffMultiplier
  zeroExtensionComparison := b.zeroExtensionComparison
theorem lifespan_eq (ν : ℝ) (Ω : Set Space) (a : SpatialField) (f : SpaceTimeField) :
    NSFormalization.Section3.T23.domainMaximalLifespan ν Ω a f = domainMaximalLifespan ν Ω a f := by
  unfold NSFormalization.Section3.T23.domainMaximalLifespan domainMaximalLifespan
  congr 1
  funext S
  have h : Nonempty (NSFormalization.Section3.T23.ClassicalSolutionOmega ν Ω a f S) ↔
      Nonempty (ClassicalSolutionOmega ν Ω a f S) :=
    ⟨fun ⟨w⟩ => ⟨solutionFrom w⟩, fun ⟨w⟩ => ⟨solutionTo w⟩⟩
  rw [propext h]

theorem maximal_eq (ν : ℝ) (Ω : Set Space) (a : SpatialField) (f u : SpaceTimeField)
    (p : SpaceTimeScalar) :
    NSFormalization.Section3.T23.IsMaximalDomainSolution ν Ω a f u p ↔ IsMaximalDomainSolution ν Ω a f u p := by
  unfold NSFormalization.Section3.T23.IsMaximalDomainSolution IsMaximalDomainSolution
  rw [lifespan_eq]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun S hS hST => ?_⟩
    obtain ⟨w, hv, hπ⟩ := h S hS hST
    exact ⟨solutionFrom w, hv, hπ⟩
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun S hS hST => ?_⟩
    obtain ⟨w, hv, hπ⟩ := h S hS hST
    exact ⟨solutionTo w, hv, hπ⟩

variable {place : DomainPlacementData P.toPacketAPI} {norms : BoundedDomainNormAPI}
  {r δ : ℝ} {D : CutoffData}
  {reference : ClassicalSolutionOmega ν Ω a g (place.T + δ)}
def apiTo (b : BoundaryInsertionAPI ν P place Ω norms a g r δ D reference) : NSFormalization.Section3.T23.BoundaryInsertionAPI ν P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound (placeTo place) Ω (normsTo norms) a g r δ (cutoffTo D) (solutionTo reference) where
  domain := b.domain
  delta_pos := b.delta_pos
  reference_force_mem := b.reference_force_mem
  initial_mem := b.initial_mem
  interiorBall_in_domain := b.interiorBall_in_domain
  ε₀ := b.ε₀
  eps_pos := b.eps_pos
  eps_le_scaling := b.eps_le_scaling
  eps_le_cutoff := b.eps_le_cutoff
  velocity := b.velocity
  pressure := b.pressure
  force := b.force
  velocity_formula := b.velocity_formula
  pressure_formula := b.pressure_formula
  force_formula := b.force_formula
  force_mem := b.force_mem
  forceDifference_mem := b.forceDifference_mem
  velocity_smooth := b.velocity_smooth
  pressure_smooth := b.pressure_smooth
  initial := b.initial
  incompressible := b.incompressible
  momentum := b.momentum
  history := b.history
  collar_agreement := b.collar_agreement
  noSlip_preserved := b.noSlip_preserved
  solution := by
    intro ε hε
    obtain ⟨w, hv, hp⟩ := b.solution ε hε
    exact ⟨solutionTo w, hv, hp⟩
  lifespan := by
    intro ε hε
    rw [lifespan_eq]
    exact b.lifespan ε hε
  maximal := fun ε hε => (maximal_eq ν Ω a (b.force ε) (b.velocity ε) (b.pressure ε)).mpr (b.maximal ε hε)
  blowup := b.blowup
  blowup_limsup := b.blowup_limsup
  crossTransport_background_advects_packet := b.crossTransport_background_advects_packet
  crossTransport_packet_advects_background := b.crossTransport_packet_advects_background
  velocityDifference_divFree := b.velocityDifference_divFree
  diffSupportRadius := b.diffSupportRadius
  diffSupportRadius_pos := b.diffSupportRadius_pos
  velocityDifference_support := b.velocityDifference_support
  diffSupport_in_chart := b.diffSupport_in_chart
  forceDifference_spatialSupport := b.forceDifference_spatialSupport
  energyConst := b.energyConst
  energyConst_nonneg := b.energyConst_nonneg
  energyRate := b.energyRate
  forceDiffSobolevConst := b.forceDiffSobolevConst
  forceDiffSobolevConst_pos := b.forceDiffSobolevConst_pos
  forceDifference_sobolev_bound := b.forceDifference_sobolev_bound
  domain_zeroExt_comparison := b.domain_zeroExt_comparison
  forceDifference_negativeSobolev_tendsto := b.forceDifference_negativeSobolev_tendsto
  forceDifference_convergence := b.forceDifference_convergence
  noSlip_uniqueness := fun a' ha f hf T₁ T₂ u₁ u₂ t ht x hx =>
    b.noSlip_uniqueness a' ha f hf T₁ T₂ (solutionFrom u₁) (solutionFrom u₂) t ht x hx

def apiFrom (b : NSFormalization.Section3.T23.BoundaryInsertionAPI ν P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound (placeTo place) Ω (normsTo norms) a g r δ (cutoffTo D) (solutionTo reference)) : BoundaryInsertionAPI ν P place Ω norms a g r δ D reference where
  domain := b.domain
  delta_pos := b.delta_pos
  reference_force_mem := b.reference_force_mem
  initial_mem := b.initial_mem
  interiorBall_in_domain := b.interiorBall_in_domain
  ε₀ := b.ε₀
  eps_pos := b.eps_pos
  eps_le_scaling := b.eps_le_scaling
  eps_le_cutoff := b.eps_le_cutoff
  velocity := b.velocity
  pressure := b.pressure
  force := b.force
  velocity_formula := b.velocity_formula
  pressure_formula := b.pressure_formula
  force_formula := b.force_formula
  force_mem := b.force_mem
  forceDifference_mem := b.forceDifference_mem
  velocity_smooth := b.velocity_smooth
  pressure_smooth := b.pressure_smooth
  initial := b.initial
  incompressible := b.incompressible
  momentum := b.momentum
  history := b.history
  collar_agreement := b.collar_agreement
  noSlip_preserved := b.noSlip_preserved
  solution := by
    intro ε hε
    obtain ⟨w, hv, hp⟩ := b.solution ε hε
    exact ⟨solutionFrom w, hv, hp⟩
  lifespan := by
    intro ε hε
    rw [← lifespan_eq]
    exact b.lifespan ε hε
  maximal := fun ε hε => (maximal_eq ν Ω a (b.force ε) (b.velocity ε) (b.pressure ε)).mp (b.maximal ε hε)
  blowup := b.blowup
  blowup_limsup := b.blowup_limsup
  crossTransport_background_advects_packet := b.crossTransport_background_advects_packet
  crossTransport_packet_advects_background := b.crossTransport_packet_advects_background
  velocityDifference_divFree := b.velocityDifference_divFree
  diffSupportRadius := b.diffSupportRadius
  diffSupportRadius_pos := b.diffSupportRadius_pos
  velocityDifference_support := b.velocityDifference_support
  diffSupport_in_chart := b.diffSupport_in_chart
  forceDifference_spatialSupport := b.forceDifference_spatialSupport
  energyConst := b.energyConst
  energyConst_nonneg := b.energyConst_nonneg
  energyRate := b.energyRate
  forceDiffSobolevConst := b.forceDiffSobolevConst
  forceDiffSobolevConst_pos := b.forceDiffSobolevConst_pos
  forceDifference_sobolev_bound := b.forceDifference_sobolev_bound
  domain_zeroExt_comparison := b.domain_zeroExt_comparison
  forceDifference_negativeSobolev_tendsto := b.forceDifference_negativeSobolev_tendsto
  forceDifference_convergence := b.forceDifference_convergence
  noSlip_uniqueness := fun a' ha f hf T₁ T₂ u₁ u₂ t ht x hx =>
    b.noSlip_uniqueness a' ha f hf T₁ T₂ (solutionTo u₁) (solutionTo u₂) t ht x hx

example (b : BoundaryInsertionAPI ν P place Ω norms a g r δ D reference) : apiFrom (apiTo b) = b := rfl
example (b : NSFormalization.Section3.T23.BoundaryInsertionAPI ν P.velocity P.pressure P.force P.carrier P.energyBound P.dissipationBound (placeTo place) Ω (normsTo norms) a g r δ (cutoffTo D) (solutionTo reference)) : apiTo (norms := norms) (apiFrom (norms := norms) b) = b := rfl


/-- The registered statement has no unconsumed supplier or insertion hypothesis. -/
theorem boundaryInsertionStatement'_of_ibp_holds :
    BlowupDensity.Contracts.V1.BoundaryInsertion.boundaryInsertionStatement'_of_ibp := by
  intro ν _hν P place Ω norms a g r δ reference hΩ hI hδ hr hg ha hrball hball
  obtain ⟨C, D, hT, hd, hx, hR, heq, hθ, hη, hplat, hrad, he, hpot, hcorr, ⟨api⟩⟩ :=
    BlowupDensity.Bindings.BoundaryInsertion.boundaryInsertionStatement'_of_ibp
      P.toPacketAPI BlowupDensity.Bindings.thresholds (placeTo place) Ω (normsTo norms)
      a g r δ (solutionTo reference) hΩ hI hδ hr hg ha hrball hball
  refine ⟨C, cutoffFrom D, hT, hd, hx, hR, heq, hθ, hη, hplat, hrad, he, hpot, hcorr, ?_⟩
  exact ⟨apiFrom (norms := norms) (D := cutoffFrom D) api⟩

theorem place_roundtrip (b : DomainPlacementData P.toPacketAPI) : placeFrom (placeTo b) = b := rfl
theorem cutoff_roundtrip (b : CutoffData) : cutoffFrom (cutoffTo b) = b := rfl
theorem solution_roundtrip (b : ClassicalSolutionOmega ν Ω a g T) : solutionFrom (solutionTo b) = b := rfl
theorem solution_roundtrip_canonical (b : NSFormalization.Section3.T23.ClassicalSolutionOmega ν Ω a g T) :
    solutionTo (solutionFrom b) = b := rfl

theorem correctedBackground_eq (v : SpaceTimeField) (w : ℝ → SpaceTimeField) (ε : ℝ) :
    correctedBackground v w ε = NSFormalization.Section3.T16.correctedBackground v w ε := rfl

theorem correctionForce_eq (ν : ℝ) (v : SpaceTimeField) (D : CutoffData) (ε : ℝ) :
    correctionForce ν v D ε = NSFormalization.Section3.T23.correctionForce ν v (cutoffTo D) ε := rfl

theorem smoothOnClosedSlab_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Set ℝ) (Ω : Set Space) (f : ℝ × Space → E) :
    SmoothOnClosedSlab I Ω f = NSFormalization.Section3.T23.SmoothOnClosedSlab I Ω f := rfl

theorem regularDomain_eq (Ω : Set Space) : IsRegularLevelDomain Ω = NSFormalization.Section3.T23.IsRegularLevelDomain Ω := rfl
theorem boxDomain_eq (Ω : Set Space) : IsBoxDomain Ω = NSFormalization.Section3.T23.IsBoxDomain Ω := rfl
theorem domain_eq (Ω : Set Space) : IsBoundedBoxOrSmoothDomain Ω = NSFormalization.Section3.T23.IsBoundedBoxOrSmoothDomain Ω := rfl
theorem initialClass_eq (Ω : Set Space) : initialClassOmega Ω = NSFormalization.Section3.T23.initialClassOmega Ω := rfl
theorem memForce_eq (Ω : Set Space) (f : SpaceTimeField) : MemForceOmega Ω f = NSFormalization.Section3.T23.MemForceOmega Ω f := rfl
theorem forceClass_eq (Ω : Set Space) : forceClassOmega Ω = NSFormalization.Section3.T23.forceClassOmega Ω := rfl
theorem ibp_eq (Ω : Set Space) : IBP Ω = NSFormalization.Section3.T23.IBP Ω := rfl

theorem energyEssSup_eq (Ω : Set Space) (T : ℝ) (f : SpaceTimeField) :
    domainEnergyEssSup Ω T f = NSFormalization.Section3.T23.domainEnergyEssSup Ω T f := rfl
theorem energyGradient_eq (Ω : Set Space) (T : ℝ) (f : SpaceTimeField) :
    domainEnergyGradient Ω T f = NSFormalization.Section3.T23.domainEnergyGradient Ω T f := rfl
theorem energyENorm_eq (Ω : Set Space) (T : ℝ) (f : SpaceTimeField) :
    domainEnergyENorm Ω T f = NSFormalization.Section3.T23.domainEnergyENorm Ω T f := rfl
theorem forceSobolev_eq (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) :
    domainForceSobolevENorm Ω s f = NSFormalization.Section3.T23.domainForceSobolevENorm Ω s f := rfl
theorem zeroExtForceSobolev_eq (Ω : Set Space) (s : ℝ) (f : SpaceTimeField) :
    zeroExtForceSobolevENorm Ω s f = NSFormalization.Section3.T23.zeroExtForceSobolevENorm Ω s f := rfl
theorem pressureMean_eq (Ω : Set Space) (p : SpaceTimeScalar) (t : ℝ) :
    domainPressureMean Ω p t = NSFormalization.Section3.T23.domainPressureMean Ω p t := rfl
theorem normalizePressure_eq (Ω : Set Space) (p : SpaceTimeScalar) :
    domainNormalizePressure Ω p = NSFormalization.Section3.T23.domainNormalizePressure Ω p := rfl

end BlowupDensity.Bindings.BoundaryInsertion.Contract
