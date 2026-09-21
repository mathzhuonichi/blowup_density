import NSFormalization.Paper1.CorrectionForceNorms
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.Semicontinuity.Basic

/-! Actual mixed Lebesgue norms of the background correction force. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionMixedNorms
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open CorrectionProfile CorrectionForceProfile
open scoped ContDiff ENNReal

def mixedNorm (p q : ℝ≥0∞) (F : VelocityField) : ℝ≥0∞ :=
  eLpNorm (fun t => (eLpNorm (fun x => F (t, x)) p volume).toReal) q volume

/-- Continuous spacetime fields give measurable spatial Lp norms, including
the essential-supremum endpoint. Fatou's theorem proves lower semicontinuity. -/
theorem spatial_norm_measurable {F : VelocityField} (hF : Continuous F) (p : ℝ≥0∞) :
    Measurable (fun t => (eLpNorm (fun x => F (t, x)) p volume).toReal) := by
  have hlsc : LowerSemicontinuous (fun t => eLpNorm (fun x => F (t, x)) p volume) := by
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro C
    apply IsSeqClosed.isClosed
    intro u t hu ht
    apply Lp.eLpNorm_le_of_ae_tendsto (u := Filter.atTop) (f := fun n x => F (u n, x))
      (Filter.Eventually.of_forall hu)
      (fun n => ((hF.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable).aestronglyMeasurable)
    apply Filter.Eventually.of_forall
    intro x
    exact ((hF.comp (continuous_id.prodMk continuous_const)).tendsto t).comp ht
  exact hlsc.measurable.ennreal_toReal

theorem eLpNorm_spatial_scale (f : Space → Space) (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) {k : ℝ} (hk : 0 < k) (x₀ : Space) :
    eLpNorm (fun x => f (k • (x - x₀))) p volume =
      ENNReal.ofReal (k ^ (-3 / p.toReal)) * eLpNorm f p volume := by
  have hmap : Measure.map (fun x : Space => k • (x - x₀)) volume =
      ENNReal.ofReal ((k ^ 3)⁻¹) • volume := by
    rw [show (fun x : Space => k • (x - x₀)) =
      (fun x : Space => k • x) ∘ (fun x => x - x₀) from rfl,
      ← Measure.map_map (by fun_prop) (by fun_prop),
      (measurePreserving_sub_right volume x₀).map_eq, Measure.map_addHaar_smul volume hk.ne']
    simp [finrank_euclideanSpace, Fintype.card_fin, abs_of_pos (inv_pos.mpr (pow_pos hk 3))]
  have hm : Measurable (fun x : Space => k • (x - x₀)) := by fun_prop
  change eLpNorm (f ∘ (fun x : Space => k • (x - x₀))) p volume = _
  rw [← eLpNorm_map_measure (μ := volume) (p := p)
    hf.aestronglyMeasurable hm.aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_zero (by positivity)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_pos (inv_pos.mpr (pow_pos hk 3))]
  congr 1
  rw [Real.inv_rpow (pow_nonneg hk.le 3), ← Real.rpow_natCast,
    ← Real.rpow_mul hk.le, ← Real.rpow_neg hk.le]
  congr 1
  norm_num [ENNReal.toReal_div]
  ring

theorem spatial_scaled_norm_real (f : Space → Space) (hf : StronglyMeasurable f)
    (p : ℝ≥0∞) {k : ℝ} (hk : 0 < k) (x₀ : Space) :
    (eLpNorm (fun x => k ^ 2 • f (k • (x - x₀))) p volume).toReal =
      k ^ (2 - 3 / p.toReal) * (eLpNorm f p volume).toReal := by
  have he : (fun x => k ^ 2 • f (k • (x - x₀))) =
      k ^ 2 • (fun x => f (k • (x - x₀))) := rfl
  rw [he, eLpNorm_const_smul, eLpNorm_spatial_scale f hf p hk x₀,
    ENNReal.toReal_mul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
    abs_of_pos (pow_pos hk 2), ENNReal.toReal_ofReal (pow_nonneg hk.le 2),
    ENNReal.toReal_ofReal (Real.rpow_nonneg hk.le _)]
  rw [← mul_assoc]
  congr 1
  conv_lhs => arg 1; rw [← Real.rpow_natCast]
  rw [← Real.rpow_add hk]
  congr 1
  ring

theorem profile_spatial_norm_bound (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p : ℝ≥0∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ,
      MemLp (fun z => forceProfile ν v x₀ T θ η (ε, σ, z)) p volume ∧
      (eLpNorm (fun z => forceProfile ν v x₀ T θ η (ε, σ, z)) p volume).toReal ≤ C := by
  obtain ⟨B, hB, hb⟩ := forceProfile_uniform_derivative_bound ν hv x₀ T hθ hη hθc hηc 0
  let g : Space → ℝ := (tsupport θ).indicator (fun _ => B)
  have hg : MemLp g p volume := memLp_indicator_const p (isClosed_tsupport θ).measurableSet B
    (Or.inr hθc.measure_ne_top)
  refine ⟨(eLpNorm g p volume).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro ε hε σ
  have hzero (z : Space) (hz : z ∉ tsupport θ) : forceProfile ν v x₀ T θ η (ε, σ, z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hz ((profile_support hv x₀ T hθ hη (forceProfile_support ν v x₀ T θ η h)).2.2)
  have hbound (z : Space) : ‖forceProfile ν v x₀ T θ η (ε, σ, z)‖ ≤ g z := by
    by_cases hz : z ∈ tsupport θ
    · simpa only [g, Set.indicator_of_mem hz, norm_iteratedFDeriv_zero] using hb ε hε (σ, z)
    · simp [g, hz, hzero z hz]
  have he := eLpNorm_mono_real (p := p) (μ := volume) hbound
  have hsm : AEStronglyMeasurable (fun z => forceProfile ν v x₀ T θ η (ε, σ, z)) volume :=
    (((forceProfile_smooth ν hv x₀ T hθ hη).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).continuous.stronglyMeasurable).aestronglyMeasurable
  exact ⟨⟨hsm, he.trans_lt hg.eLpNorm_lt_top⟩, ENNReal.toReal_mono hg.eLpNorm_lt_top.ne he⟩

theorem physical_force_spatial_norm (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (hε : 0 < ε) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) (p : ℝ≥0∞) :
    (eLpNorm (fun x => Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) (t, x))
      p volume).toReal = (ε⁻¹) ^ (2 - 3 / p.toReal) *
      (eLpNorm (fun z => forceProfile ν v x₀ T θ η
        (ε, (ε⁻¹) ^ 2 * (t - T), z)) p volume).toReal := by
  have heq : (fun x => Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) (t, x)) =
      fun x => (ε⁻¹) ^ 2 • forceProfile ν v x₀ T θ η
        (ε, (ε⁻¹) ^ 2 * (t - T), ε⁻¹ • (x - x₀)) := by
    funext x
    simpa only [inv_pow, inverseScale_apply, Prod.fst_sub, Prod.snd_sub] using
      physicalForce_eq_profile ν hv x₀ T ε hε.ne' hθ hη (t, x)
  rw [heq]
  exact spatial_scaled_norm_real _
    (((forceProfile_smooth ν hv x₀ T hθ hη).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).continuous.stronglyMeasurable)
    p (inv_pos.mpr hε) x₀

/-- The genuine mixed Lebesgue correction estimate, including both essential
supremum endpoints through the convention `1 / infinity = 0`. -/
theorem physical_force_mixed_bound (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      mixedNorm p q (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) ≤
        ENNReal.ofReal (ε ^ (-2 + 3 / p.toReal + 2 / q.toReal)) * C := by
  obtain ⟨B, hB, hb⟩ := profile_spatial_norm_bound ν hv x₀ T hθ hη hθc hηc p
  let g : ℝ → ℝ := (tsupport η).indicator (fun _ => B)
  have hg : MemLp g q volume := memLp_indicator_const q (isClosed_tsupport η).measurableSet B
    (Or.inr hηc.measure_ne_top)
  refine ⟨eLpNorm g q volume, hg.eLpNorm_lt_top, ?_⟩
  intro ε hε
  have hgsm : StronglyMeasurable g := stronglyMeasurable_const.indicator (isClosed_tsupport η).measurableSet
  have h := Source.eLpNorm_parabolic_majorant (a := 2 - 3 / p.toReal) (inv_pos.mpr hε.1) T q
    (fun t => (eLpNorm (fun x => Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε) (t, x)) p volume).toReal) g hgsm ?_
  · have he : (ε⁻¹) ^ (2 - 3 / p.toReal - 2 / q.toReal) =
        ε ^ (-2 + 3 / p.toReal + 2 / q.toReal) := by
      rw [Real.inv_rpow hε.1.le, ← Real.rpow_neg hε.1.le]
      congr 1
      ring
    simpa only [mixedNorm, he] using h
  · intro t
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      physical_force_spatial_norm ν hv x₀ T ε t hε.1 hθ hη p]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (inv_nonneg.mpr hε.1.le) _)
    let σ := (ε⁻¹) ^ 2 * (t - T)
    change (eLpNorm (fun z => forceProfile ν v x₀ T θ η (ε, σ, z)) p volume).toReal ≤ g σ
    by_cases hσ : σ ∈ tsupport η
    · simpa only [g, Set.indicator_of_mem hσ] using (hb ε ⟨hε.1.le, hε.2⟩ σ).2
    · have hz : (fun z => forceProfile ν v x₀ T θ η (ε, σ, z)) = 0 := by
        funext z
        apply image_eq_zero_of_notMem_tsupport
        intro h
        exact hσ ((profile_support hv x₀ T hθ hη (forceProfile_support ν v x₀ T θ η h)).2.1)
      change (eLpNorm (fun z => forceProfile ν v x₀ T θ η (ε, σ, z)) p volume).toReal ≤ g σ
      simp [hz, g, hσ]

/-- Every physical spatial norm used in `mixedNorm` is finite. Thus taking
its real value never invokes the convention `infinity.toReal = 0`. -/
theorem physical_force_spatial_memLp (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε t : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p : ℝ≥0∞) :
    MemLp (fun x => Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) (t, x)) p volume := by
  obtain ⟨_, _, hb⟩ := profile_spatial_norm_bound ν hv x₀ T hθ hη hθc hηc p
  let f : Space → Space := fun z => forceProfile ν v x₀ T θ η (ε, (ε⁻¹) ^ 2 * (t - T), z)
  have hf : ContDiff ℝ ∞ f := (forceProfile_smooth ν hv x₀ T hθ hη).comp
    (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))
  have hi : MemLp f p volume := (hb ε ⟨hε.1.le, hε.2⟩ _).1
  have heq : (fun x => Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) (t, x)) =
      (ε⁻¹) ^ 2 • (fun x => f (ε⁻¹ • (x - x₀))) := by
    funext x
    simpa only [f, Pi.smul_apply, inv_pow, inverseScale_apply, Prod.fst_sub, Prod.snd_sub] using
      physicalForce_eq_profile ν hv x₀ T ε hε.1.ne' hθ hη (t, x)
  rw [heq]
  refine ⟨(((hf.comp ((contDiff_id.sub contDiff_const).const_smul ε⁻¹)).const_smul
    ((ε⁻¹) ^ 2)).continuous.stronglyMeasurable).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_const_smul, eLpNorm_spatial_scale f hf.continuous.stronglyMeasurable p
    (inv_pos.mpr hε.1) x₀]
  exact ENNReal.mul_lt_top (by finiteness)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hi.eLpNorm_lt_top)

theorem physical_force_mixed_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p q : ℝ≥0∞)
    (hβ : 0 < -2 + 3 / p.toReal + 2 / q.toReal) :
    Filter.Tendsto (fun ε => mixedNorm p q
      (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q
  exact Source.ennreal_tendsto_zero_of_power_bound hβ hC.ne
    (fun ε hε hε1 => hb ε ⟨hε, hε1⟩)

/-- The mixed time norm is a genuine `MemLp` norm of a measurable, finite
spatial-norm function, for all spatial and temporal exponents. -/
theorem physical_force_mixed_memLp (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) 1)
    {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (p q : ℝ≥0∞) :
    MemLp (fun t => (eLpNorm (fun x => Source.correctionForce ν v
      (physicalCorrection v x₀ T θ η ε) (t, x)) p volume).toReal) q volume := by
  obtain ⟨C, hC, hb⟩ := physical_force_mixed_bound ν hv x₀ T hθ hη hθc hηc p q
  have hcont : Continuous (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε)) := by
    have heq : Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) =
        fun z => (ε ^ 2)⁻¹ • forceProfile ν v x₀ T θ η (ε, inverseScale ε (z - (T, x₀))) :=
      funext (physicalForce_eq_profile ν hv x₀ T ε hε.1.ne' hθ hη)
    rw [heq]
    exact (continuous_const (y := (ε ^ 2)⁻¹)).smul ((forceProfile_smooth ν hv x₀ T hθ hη).continuous.comp
      ((continuous_const (y := ε)).prodMk ((inverseScale ε).continuous.comp (continuous_id.sub continuous_const))))
  exact ⟨(spatial_norm_measurable hcont p).stronglyMeasurable.aestronglyMeasurable,
    (hb ε hε).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC)⟩

end NSFormalization.Paper1.CorrectionMixedNorms
