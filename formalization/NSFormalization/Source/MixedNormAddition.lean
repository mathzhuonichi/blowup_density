import NSFormalization.Source.MixedForceScaling

/-! Triangle inequality for actual nested mixed Lebesgue norms. Compactness
certifies finite spatial norms before taking their real values. -/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory Filter Topology
open Paper1.CorrectionMixedNorms
open scoped ContDiff ENNReal

theorem mixedNorm_add_le {F G : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    (hFc : HasCompactSupport F) (hGc : HasCompactSupport G)
    (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    mixedNorm p q (F + G) ≤ mixedNorm p q F + mixedNorm p q G := by
  obtain ⟨_, _, hFi⟩ := compact_spatial_norm_uniform hF.continuous hFc p
  obtain ⟨_, _, hGi⟩ := compact_spatial_norm_uniform hG.continuous hGc p
  apply (eLpNorm_mono_real (p := q) (μ := volume)
    (f := fun t => (eLpNorm (fun x => (F + G) (t, x)) p volume).toReal)
    (g := fun t => (eLpNorm (fun x => F (t, x)) p volume).toReal +
      (eLpNorm (fun x => G (t, x)) p volume).toReal) (fun t => ?_)).trans
  · exact eLpNorm_add_le (spatial_norm_measurable hF.continuous p).aestronglyMeasurable
      (spatial_norm_measurable hG.continuous p).aestronglyMeasurable hq
  · rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    have h := eLpNorm_add_le (hFi t).1.aestronglyMeasurable (hGi t).1.aestronglyMeasurable hp
    have hh := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨(hFi t).1.eLpNorm_ne_top, (hGi t).1.eLpNorm_ne_top⟩) h
    rw [ENNReal.toReal_add (hFi t).1.eLpNorm_ne_top (hGi t).1.eLpNorm_ne_top] at hh
    exact hh

theorem mixed_family_add_tendsto_zero (p q : ℝ≥0∞) (hp : 1 ≤ p) (hq : 1 ≤ q)
    {F G : ℝ → VelocityField}
    (hF : ∀ ε, ContDiff ℝ ∞ (F ε)) (hG : ∀ ε, ContDiff ℝ ∞ (G ε))
    (hFc : ∀ ε, 0 < ε → HasCompactSupport (F ε))
    (hGc : ∀ ε, 0 < ε → HasCompactSupport (G ε))
    (hFlim : Tendsto (fun ε : ℝ => mixedNorm p q (F ε)) (𝓝[>] 0) (𝓝 0))
    (hGlim : Tendsto (fun ε : ℝ => mixedNorm p q (G ε)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => mixedNorm p q (F ε + G ε)) (𝓝[>] 0) (𝓝 0) := by
  have hlim := hFlim.add hGlim
  simp only [add_zero] at hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · exact Eventually.of_forall (fun _ => bot_le)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact mixedNorm_add_le (hF ε) (hG ε) (hFc ε hε) (hGc ε hε) p q hp hq

end NSFormalization.Source
