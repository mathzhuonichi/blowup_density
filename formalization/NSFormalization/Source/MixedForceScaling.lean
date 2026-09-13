import NSFormalization.Paper1.CorrectionMixedNorms
import NSFormalization.Source.AngularForceNorms

/-! Physical mixed Lebesgue concentration of a compact force, including both
essential-supremum endpoints. All spatial norms are certified finite. -/
noncomputable section
namespace NSFormalization.Source
open NavierStokes.ProblemStatement MeasureTheory Set
open Paper1.CorrectionMixedNorms
open scoped ContDiff ENNReal

theorem spatial_force_norm_real (f : Space → Space) (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) {k : ℝ} (hk : 0 < k) (x₀ : Space) :
    (eLpNorm (fun x => k ^ 3 • f (k • (x - x₀))) p volume).toReal =
      k ^ (3 - 3 / p.toReal) * (eLpNorm f p volume).toReal := by
  rw [show (fun x => k ^ 3 • f (k • (x - x₀))) =
      k ^ 3 • (fun x => f (k • (x - x₀))) from rfl,
    eLpNorm_const_smul, eLpNorm_spatial_scale f hf p hk x₀,
    ENNReal.toReal_mul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
    abs_of_pos (pow_pos hk 3), ENNReal.toReal_ofReal (pow_nonneg hk.le 3),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hk.le _)]
  rw [← mul_assoc]
  congr 1
  conv_lhs => arg 1; rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hk]
  congr 1
  ring

theorem compact_spatial_norm_uniform {F : VelocityField}
    (hF : Continuous F) (hc : HasCompactSupport F) (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      MemLp (fun x => F (t, x)) p volume ∧
      (eLpNorm (fun x => F (t, x)) p volume).toReal ≤ C := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hF
  let K := Prod.snd '' tsupport F
  have hK : IsCompact K := hc.isCompact.image continuous_snd
  let g : Space → ℝ := K.indicator (fun _ => B)
  have hg : MemLp g p volume := memLp_indicator_const p hK.measurableSet B
    (Or.inr hK.measure_ne_top)
  have hb (t : ℝ) (x : Space) : ‖F (t, x)‖ ≤ g x := by
    by_cases hx : x ∈ K
    · simpa only [g, indicator_of_mem hx] using hB (t, x)
    · have hz : F (t, x) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hx ⟨(t, x), h, rfl⟩)
      simp [g, hx, hz]
  refine ⟨(eLpNorm g p volume).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro t
  have hm := eLpNorm_mono_real (p := p) (μ := volume) (hb t)
  exact ⟨⟨(hF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable,
    hm.trans_lt hg.eLpNorm_lt_top⟩, ENNReal.toReal_mono hg.eLpNorm_ne_top hm⟩

/-- Actual finite spatial norms for the parabolically concentrated vector force. -/
theorem compact_parabolic_force_spatial_memLp {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (k t₀ : ℝ) (x₀ : Space) (t : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x => parabolicForce k t₀ x₀ F (t, x)) p volume := by
  obtain ⟨_, _, h⟩ := compact_spatial_norm_uniform
    (parabolicForce_smooth k t₀ x₀ hF).continuous (parabolicForce_compact k t₀ x₀ hc) p
  exact (h t).1

/-- The constant is uniform in both insertion centers and epsilon. -/
theorem compact_force_mixed_bound {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (p q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε : ℝ, 0 < ε → ∀ t₀ : ℝ, ∀ x₀ : Space,
      mixedNorm p q (parabolicForce ε⁻¹ t₀ x₀ F) ≤
        ENNReal.ofReal (ε ^ (-3 + 3 / p.toReal + 2 / q.toReal)) * C := by
  obtain ⟨B, hB, hb⟩ := compact_spatial_norm_uniform hF.continuous hc p
  let K := Prod.fst '' tsupport F
  have hK : IsCompact K := hc.isCompact.image continuous_fst
  let g : ℝ → ℝ := K.indicator (fun _ => B)
  have hg : MemLp g q volume := memLp_indicator_const q hK.measurableSet B
    (Or.inr hK.measure_ne_top)
  have hbound (t : ℝ) : (eLpNorm (fun x => F (t, x)) p volume).toReal ≤ g t := by
    by_cases ht : t ∈ K
    · simpa only [g, indicator_of_mem ht] using (hb t).2
    · have hz : (fun x => F (t, x)) = 0 := by
        funext x
        exact image_eq_zero_of_notMem_tsupport (fun h => ht ⟨(t, x), h, rfl⟩)
      simp [g, ht, hz]
  refine ⟨eLpNorm g q volume, hg.eLpNorm_lt_top, ?_⟩
  intro ε hε t₀ x₀
  have hm := eLpNorm_parabolic_majorant (a := 3 - 3 / p.toReal) (inv_pos.mpr hε) t₀ q
    (fun t => (eLpNorm (fun x => parabolicForce ε⁻¹ t₀ x₀ F (t, x)) p volume).toReal)
    g (stronglyMeasurable_const.indicator hK.measurableSet) ?_
  · have he : (ε⁻¹) ^ (3 - 3 / p.toReal - 2 / q.toReal) =
        ε ^ (-3 + 3 / p.toReal + 2 / q.toReal) := by
      rw [Real.inv_rpow hε.le, ← Real.rpow_neg hε.le]
      congr 1
      ring
    simpa only [mixedNorm, he] using hm
  · intro t
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    change (eLpNorm (fun x => (ε⁻¹) ^ 3 •
      F ((ε⁻¹) ^ 2 * (t - t₀), ε⁻¹ • (x - x₀))) p volume).toReal ≤ _
    rw [spatial_force_norm_real (fun x => F ((ε⁻¹) ^ 2 * (t - t₀), x))
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable p
      (inv_pos.mpr hε) x₀]
    exact mul_le_mul_of_nonneg_left (hbound _) (Real.rpow_nonneg (inv_nonneg.mpr hε.le) _)

theorem compact_force_mixed_tendsto_zero {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (p q : ℝ≥0∞)
    (hβ : 0 < -3 + 3 / p.toReal + 2 / q.toReal)
    (center : ℝ → ℝ) (spatialCenter : ℝ → Space) :
    Filter.Tendsto (fun ε => mixedNorm p q
      (parabolicForce ε⁻¹ (center ε) (spatialCenter ε) F))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := compact_force_mixed_bound hF hc p q
  exact ennreal_tendsto_zero_of_power_bound hβ hC.ne
    (fun ε hε _ => hb ε hε (center ε) (spatialCenter ε))

/-- A compact smooth physical force has an actual finite outer time norm,
and its spatial norm profile is measurable for every p, including infinity. -/
theorem compact_mixed_memLp {F : VelocityField}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (p q : ℝ≥0∞) :
    MemLp (fun t => (eLpNorm (fun x => F (t, x)) p volume).toReal) q volume := by
  obtain ⟨C, hC, hb⟩ := compact_force_mixed_bound hF hc p q
  have he : parabolicForce 1 0 0 F = F := by
    funext z
    simp [parabolicForce, dilateField]
  have h := hb 1 zero_lt_one 0 0
  rw [inv_one, he] at h
  simp only [Real.one_rpow, ENNReal.ofReal_one, one_mul] at h
  exact ⟨(spatial_norm_measurable hF.continuous p).aestronglyMeasurable, h.trans_lt hC⟩

end NSFormalization.Source
