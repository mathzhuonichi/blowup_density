import NSFormalization.Section3.T23.MatchingSupplier
import NSFormalization.Paper1.CorrectionEnergy
import NSFormalization.Paper1.CorrectionVectorNorms
import NSFormalization.Section4.D01.HalfOrder
import NSFormalization.Section4.I03.Angular

/-! Quantitative estimates for the same local correction family. -/
noncomputable section
namespace NSFormalization.Section3.T23

open Set MeasureTheory Filter
open NavierStokes NavierStokes.ProblemStatement
open scoped ENNReal

/-- Restricting space decreases both summands of the exact energy norm. -/
theorem domainEnergyENorm_le (Ω : Set Space) (T : ℝ) (w : VelocityField) :
    domainEnergyENorm Ω T w ≤ NSFormalization.Section3.T24.energyENorm T w := by
  apply add_le_add
  · exact essSup_mono_ae (Filter.Eventually.of_forall fun _ =>
      eLpNorm_mono_measure _ Measure.restrict_le_self)
  · apply ENNReal.rpow_le_rpow _ (by positivity)
    apply lintegral_mono
    intro t
    exact ENNReal.rpow_le_rpow (eLpNorm_mono_measure _ Measure.restrict_le_self) (by norm_num)

/-- I02 energy transported to the actual local family; the constant is
nonnegative, and also bounds the restricted-domain energy. -/
theorem WholeSpaceCorrectionAPI.local_energy_bound {ν : ℝ} {u v : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K)
    (heq : EqOn v C.v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ Metric.ball C.x₀ C.r))
    {e : ℝ} (he : e ≤ C.ε₀) :
    let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ε ∈ Ioc (0 : ℝ) e,
      NSFormalization.Section3.T24.energyENorm C.T (D.correction ε) ≤
        ENNReal.ofReal (B * ε ^ ((3 : ℝ) / 2)) ∧
      ∀ Ω : Set Space, domainEnergyENorm Ω C.T (D.correction ε) ≤
        ENNReal.ofReal (B * ε ^ ((3 : ℝ) / 2)) := by
  refine ⟨max C.energyConst 0, le_max_right _ _, ?_⟩
  intro ε hε
  have hεC : ε ∈ Ioc (0 : ℝ) C.ε₀ := ⟨hε.1, hε.2.trans he⟩
  have hb := (C.correction_energy_bound ε hεC).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left C.energyConst 0)
      (Real.rpow_nonneg hε.1.le _)))
  rw [(C.local_match heq hεC).1]
  exact ⟨hb, fun Ω => (domainEnergyENorm_le Ω C.T (C.correction ε)).trans hb⟩

/-- The mixed norm uses the same correction force and the same cutoff;
both essential-supremum endpoints are included. -/
theorem WholeSpaceCorrectionAPI.local_mixed_bound {ν : ℝ} {u v : VelocityField}
    {K : Set Space} (C : WholeSpaceCorrectionAPI ν u K)
    (heq : EqOn v C.v (Ioo (0 : ℝ) (C.T + C.δ) ×ˢ Metric.ball C.x₀ C.r))
    {e : ℝ} (he : e ≤ C.ε₀) (p q : ℝ≥0∞) [Fact (1 ≤ p)] :
    let D := localCorrectionData v C.x₀ C.T C.θ C.η C.plateau C.θRadius e
    ∃ B : ℝ, 0 < B ∧ ∀ ε ∈ Ioc (0 : ℝ) e,
      NSFormalization.Section3.T15.mixedLebesgueENorm q p (correctionForce ν v D ε) ≤
        ENNReal.ofReal (B * ε ^ (NSFormalization.Section3.T15.alphaT p q + 1)) := by
  refine ⟨max (C.mixedConst p q) 0 + 1, by positivity, ?_⟩
  intro ε hε
  have hεC : ε ∈ Ioc (0 : ℝ) C.ε₀ := ⟨hε.1, hε.2.trans he⟩
  rw [(C.local_match heq hεC).2]
  apply (C.force_mixed_bound p q ε hεC).trans
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hε.1.le _)
  exact (le_max_left _ _).trans (by linarith)

open scoped ContDiff

/-- Test the registered path infimum against the actual angular datum path.
This does not identify it with a slice-integral norm. -/
theorem forceSobolevENorm_le_cycles (s : ℝ) (q : ℝ≥0∞) {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    NSFormalization.Section4.D01.forceSobolevENorm q s F ≤
      ENNReal.ofReal (NSFormalization.Source.frequencyUnit ^ |s|) *
        eLpNorm (NSFormalization.Source.vectorFourierSobolevNorm s F) q volume := by
  refine le_trans (iInf_le _ ⟨NSFormalization.Section4.I03.angularPath s F hF hc,
    fun t _ i ψ => NSFormalization.Section4.I03.angularPath_pairing s F hF hc t i ψ,
    (NSFormalization.Section4.I03.memLp_angularPath s F hF hc q).aestronglyMeasurable⟩) ?_
  exact NSFormalization.Section4.I03.eLpNorm_angularPath_le s F hF hc q

/-- One threshold, chosen before q and s, gives the local Sobolev-force rate.
The global extension is constructed from local smoothness and divergence. -/
theorem exists_local_sobolev_bounds (ν : ℝ) {v : VelocityField}
    {x₀ : Space} {r T δ R : ℝ} {θ : Space → ℝ} {η : ℝ → ℝ}
    (hr : 0 < r) (hT : 0 < T) (hδ : 0 < δ) (hR : 0 < R)
    (hv : ContDiffOn ℝ ∞ v (Ioo (0 : ℝ) (T + δ) ×ˢ Metric.ball x₀ r))
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) (T + δ), ∀ x ∈ Metric.ball x₀ r,
      spatialDivergence v t x = 0)
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η)
    (hθs : tsupport θ ⊆ Metric.ball (0 : Space) R)
    (hηs : tsupport η ⊆ Ioo (-2 : ℝ) 2) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ ∀ q : ℝ≥0∞, 1 ≤ q →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∃ B : ℝ, 0 < B ∧
        ∀ ε ∈ Ioc (0 : ℝ) e,
          NSFormalization.Section4.D01.forceSobolevENorm q s
            (NSFormalization.Source.correctionForce ν v
              (NSFormalization.Paper1.CorrectionProfile.physicalCorrection v x₀ T θ η ε)) ≤
            ENNReal.ofReal (B *
              (ε ^ (2 / q.toReal - 1 / 2) + ε ^ (2 / q.toReal - 1 / 2 - s))) := by
  obtain ⟨V, e, hV, _, he, he1, heq⟩ := exists_matching_global_correction
    ν hr hT hδ hR hv hdiv hθc hηc hθs hηs
  refine ⟨e, he, he1, ?_⟩
  intro q hq s hs hs1
  obtain ⟨L, hL, hb⟩ :=
    NSFormalization.Paper1.CorrectionForceNorms.vectorPhysicalForce_uniform_positive_time
      ν hV x₀ T hθ hη hθc hηc hs1 hs q hq
  let b := NSFormalization.Source.frequencyUnit ^ |s| * L.toReal
  have hb0 : 0 ≤ b := mul_nonneg
    (Real.rpow_nonneg NSFormalization.Source.frequencyUnit_pos.le _) ENNReal.toReal_nonneg
  refine ⟨b + 1, by linarith, ?_⟩
  intro ε hε
  rw [(heq ε hε).2]
  have hF := NSFormalization.Paper1.CorrectionForceNorms.physicalForce_smooth
    ν hV x₀ T ε hθ hη
  have hc := NSFormalization.Paper1.CorrectionForceNorms.physicalForce_compact
    ν V x₀ T ε hε.1.ne' hθc hηc
  have hrpow := Real.rpow_nonneg hε.1.le (2 / q.toReal - 1 / 2 - s)
  calc
    _ ≤ ENNReal.ofReal (NSFormalization.Source.frequencyUnit ^ |s|) *
        (ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * L) :=
      (forceSobolevENorm_le_cycles s q hF hc).trans
        (mul_le_mul_right (hb ε ⟨hε.1, hε.2.trans he1⟩) _)
    _ = ENNReal.ofReal (b * ε ^ (2 / q.toReal - 1 / 2 - s)) := by
      dsimp only [b]
      rw [ENNReal.ofReal_mul (mul_nonneg
        (Real.rpow_nonneg NSFormalization.Source.frequencyUnit_pos.le _) ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul (Real.rpow_nonneg NSFormalization.Source.frequencyUnit_pos.le _),
        ENNReal.ofReal_toReal hL.ne]
      ring
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [Real.rpow_nonneg hε.1.le (2 / q.toReal - 1 / 2),
        mul_nonneg hb0 (Real.rpow_nonneg hε.1.le (2 / q.toReal - 1 / 2))]

end NSFormalization.Section3.T23
