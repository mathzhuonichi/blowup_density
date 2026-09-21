import NSFormalization.Paper1.CorrectionProfile
import NSFormalization.Source.PacketScaling

/-! Fixed rescaled cutoffs give an actual physical removal at every positive scale. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace NSFormalization.Source.PhysicalRemoval
open NavierStokes.ProblemStatement NSFormalization.Paper1
open CorrectionProfile PacketScaling

theorem physical_smooth {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T ε : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) :
    ContDiff ℝ ∞ (physicalCorrection v x₀ T θ η ε) :=
  localCorrection_smooth hv x₀
    (hθ.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹))
    (hη.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))

theorem physical_divergence {v : VelocityField} (hv : ContDiff ℝ ∞ v) (x₀ : Space) (T ε : ℝ)
    {θ : Space → ℝ} (η : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) :
    ∀ t x, spatialDivergence (physicalCorrection v x₀ T θ η ε) t x = 0 :=
  localCorrection_divergence hv x₀
    (hθ.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹))

def spaceMap (ε : ℝ) (x₀ : Space) (y : Space) : Space := x₀ + ε • y

def timeMap (ε T s : ℝ) : ℝ := T + ε ^ 2 * s

theorem spatial_cutoff_support {ε : ℝ} (hε : ε ≠ 0) (x₀ : Space)
    {θ : Space → ℝ} (hc : HasCompactSupport θ) :
    tsupport (spatialCutoff θ x₀ ε) ⊆ spaceMap ε x₀ '' tsupport θ := by
  apply closure_minimal _ (hc.isCompact.image (by unfold spaceMap; fun_prop)).isClosed
  intro x hx
  refine ⟨ε⁻¹ • (x - x₀), subset_tsupport θ hx, ?_⟩
  simp only [spaceMap, smul_smul, mul_inv_cancel₀ hε, one_smul]
  abel

theorem temporal_cutoff_support {ε : ℝ} (hε : ε ≠ 0) (T : ℝ)
    {η : ℝ → ℝ} (hc : HasCompactSupport η) :
    tsupport (temporalCutoff η T ε) ⊆ timeMap ε T '' tsupport η := by
  apply closure_minimal _ (hc.isCompact.image (by unfold timeMap; fun_prop)).isClosed
  intro t ht
  refine ⟨(ε ^ 2)⁻¹ * (t - T), subset_tsupport η ht, ?_⟩
  simp only [timeMap, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hε), one_mul]
  ring

theorem physical_compact {ε : ℝ} (hε : ε ≠ 0) (v : VelocityField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : HasCompactSupport θ) (hη : HasCompactSupport η) :
    HasCompactSupport (physicalCorrection v x₀ T θ η ε) := by
  apply localCorrection_compact
  · exact (hθ.isCompact.image (by unfold spaceMap; fun_prop : Continuous (spaceMap ε x₀))).of_isClosed_subset
      (isClosed_tsupport _) (spatial_cutoff_support hε x₀ hθ)
  · exact (hη.isCompact.image (by unfold timeMap; fun_prop : Continuous (timeMap ε T))).of_isClosed_subset
      (isClosed_tsupport _) (temporal_cutoff_support hε T hη)

theorem physical_support {ε R : ℝ} (hε : 0 < ε) (v : VelocityField) (x₀ : Space) (T : ℝ)
    {θ : Space → ℝ} {η : ℝ → ℝ} (hθ : HasCompactSupport θ) (hη : HasCompactSupport η)
    (hθR : tsupport θ ⊆ Metric.ball 0 R) (hηI : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    tsupport (physicalCorrection v x₀ T θ η ε) ⊆
      Ioo (T - 2 * ε ^ 2) (T + 2 * ε ^ 2) ×ˢ Metric.ball x₀ (ε * R) := by
  intro z hz
  obtain ⟨ht, hx⟩ := localCorrection_support v x₀ _ _ hz
  obtain ⟨s, hs, he⟩ := temporal_cutoff_support hε.ne' T hη ht
  obtain ⟨y, hy, hey⟩ := spatial_cutoff_support hε.ne' x₀ hθ hx
  have hs' := hηI hs
  have hy' := hθR hy
  constructor
  · change T + ε ^ 2 * s = z.1 at he
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hs'.1 (sq_pos_of_pos hε)]
    · nlinarith [mul_lt_mul_of_pos_left hs'.2 (sq_pos_of_pos hε)]
  · rw [Metric.mem_ball, ← hey]
    have hyN : ‖y‖ < R := by simpa using hy'
    simpa [spaceMap, dist_eq_norm, norm_smul, abs_of_pos hε] using mul_lt_mul_of_pos_left hyN hε

/-- The fixed spatial plateau is transported by the physical scaling. -/
theorem physical_removes {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (hdiv : ∀ t x, spatialDivergence v t x = 0)
    (x₀ : Space) (T : ℝ) {ε : ℝ} (hε : 0 < ε)
    (θ : Space → ℝ) (η : ℝ → ℝ) {O : Set Space} (hO : IsOpen O)
    (hθone : EqOn θ (fun _ => 1) O) (hηone : EqOn η (fun _ => 1) (Icc (-1 : ℝ) 1)) :
    ∀ t ∈ Icc (T - ε ^ 2) (T + ε ^ 2), ∀ x ∈ spaceMap ε x₀ '' O,
      ∀ᶠ y in 𝓝 x, v (t, y) + physicalCorrection v x₀ T θ η ε (t, y) = 0 := by
  intro t ht x hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hηt : temporalCutoff η T ε t = 1 := by
    apply hηone
    change -1 ≤ (ε ^ 2)⁻¹ * (t - T) ∧ (ε ^ 2)⁻¹ * (t - T) ≤ 1
    have hp := sq_pos_of_pos hε
    rw [mul_comm, ← div_eq_mul_inv]
    constructor
    · apply (le_div_iff₀ hp).mpr
      linarith [ht.1]
    · apply (div_le_iff₀ hp).mpr
      linarith [ht.2]
  let A : Space → Space := fun y => ε⁻¹ • (y - x₀)
  have hA : Continuous A := by fun_prop
  have hAz : A (spaceMap ε x₀ z) ∈ O := by
    simpa [A, spaceMap, smul_smul, hε.ne'] using hz
  have hneigh : ∀ᶠ y in 𝓝 (spaceMap ε x₀ z), A y ∈ O :=
    hA.continuousAt.preimage_mem_nhds (hO.mem_nhds hAz)
  filter_upwards [hneigh] with y hy
  have hχy : ∀ᶠ z in 𝓝 y, spatialCutoff θ x₀ ε z = 1 := by
    filter_upwards [hA.continuousAt.preimage_mem_nhds (hO.mem_nhds hy)] with z hz
    exact hθone hz
  rw [physicalCorrection, localCorrection_eq_neg hv hdiv x₀ _ _ t y hηt hχy]
  exact add_neg_cancel _

end NSFormalization.Source.PhysicalRemoval
