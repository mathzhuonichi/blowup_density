import NSFormalization.Section3.T23.Assembly
import NSFormalization.Section3.T23.CorrectionEstimates
import Bindings.CorrectionV2
import Bindings.Scaling

/-! T23 supplier preparation only; this module does not register or prove the
48-field boundary insertion statement. Migrated from lane 481. -/
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

end BlowupDensity.Bindings.BoundaryInsertion
