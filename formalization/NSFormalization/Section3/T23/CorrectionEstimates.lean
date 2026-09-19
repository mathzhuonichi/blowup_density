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

end NSFormalization.Section3.T23
