import NSFormalization.Paper1.CorrectionEnergy
import NSFormalization.Paper3.HomogeneousTime
import NSFormalization.Source.FourierTranslation

/-! Uniform physical moment bounds for the actual correction-force profiles. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionForceNorms
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open CorrectionProfile CorrectionForceProfile CorrectionEnergy
open scoped ContDiff ENNReal FourierTransform

def scalarProfile (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (i : Fin 3) (p : Parameter) : ℂ :=
  (forceProfile ν v x₀ T θ η p i : ℂ)

theorem scalarProfile_smooth (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) (i : Fin 3) :
    ContDiff ℝ ∞ (scalarProfile ν v x₀ T θ η i) :=
  Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp
    (forceProfile_smooth ν hv x₀ T hθ hη))

theorem scalarProfile_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) (i : Fin 3) (ε : ℝ)
    (z : SpaceTime) (hz : z ∉ tsupport η ×ˢ tsupport θ) :
    scalarProfile ν v x₀ T θ η i (ε, z) = 0 := by
  have hn : (ε, z) ∉ tsupport (forceProfile ν v x₀ T θ η) :=
    fun h => hz ((profile_support hv x₀ T hθ hη (forceProfile_support ν v x₀ T θ η h)).2)
  simp [scalarProfile, image_eq_zero_of_notMem_tsupport hn]

theorem scalarProfile_slice_compact (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3) (ε : ℝ) :
    HasCompactSupport (fun z : SpaceTime => scalarProfile ν v x₀ T θ η i (ε, z)) :=
  HasCompactSupport.intro (hηc.prod hθc) (scalarProfile_zero ν hv x₀ T hθ hη i ε)

theorem scalarProfile_uniform_bound (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ z : SpaceTime,
      ‖scalarProfile ν v x₀ T θ η i (ε, z)‖ ≤ C := by
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod (hηc.prod hθc)).exists_bound_of_continuousOn
    (scalarProfile_smooth ν hv x₀ T hθ hη i).continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro ε hε z
  by_cases hz : z ∈ tsupport η ×ˢ tsupport θ
  · exact (hb (ε, z) ⟨hε, hz⟩).trans (le_max_left _ _)
  · rw [scalarProfile_zero ν hv x₀ T hθ hη i ε z hz, norm_zero]
    exact le_max_right _ _

theorem scalarProfile_uniform_moments (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    (n : ℕ) (hn : n ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ,
      (∫ z : Space, ‖scalarProfile ν v x₀ T θ η i (ε, σ, z)‖ ^ n) ≤ C := by
  obtain ⟨B, hB, hb⟩ := scalarProfile_uniform_bound ν hv x₀ T hθ hη hθc hηc i
  refine ⟨volume.real (tsupport θ) * B ^ n, by positivity, ?_⟩
  intro ε hε σ
  have hg : Integrable ((tsupport θ).indicator (fun _ : Space => B ^ n)) := by
    rw [integrable_indicator_iff (isClosed_tsupport θ).measurableSet]
    exact integrableOn_const hθc.measure_ne_top
  calc
    _ ≤ ∫ z : Space, (tsupport θ).indicator (fun _ => B ^ n) z := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => pow_nonneg (norm_nonneg _) n) hg
      apply Filter.Eventually.of_forall
      intro z
      by_cases hz : z ∈ tsupport θ
      · simpa [hz] using pow_le_pow_left₀ (norm_nonneg _) (hb ε hε (σ, z)) n
      · have hzero := scalarProfile_zero ν hv x₀ T hθ hη i ε (σ, z) (fun h => hz h.2)
        simp [hz, hzero, hn]
    _ = _ := by rw [integral_indicator_const _ (isClosed_tsupport θ).measurableSet]; rfl

theorem scalarProfile_uniform_homogeneous (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ,
      Source.homogeneousFourierNorm s (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z)) ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := scalarProfile_uniform_moments ν hv x₀ T hθ hη hθc hηc i 1 (by norm_num)
  obtain ⟨C₂, _, h₂⟩ := scalarProfile_uniform_moments ν hv x₀ T hθ hη hθc hηc i 2 (by norm_num)
  refine ⟨Real.sqrt (C₁ ^ 2 * (∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)) + C₂),
    Real.sqrt_nonneg _, ?_⟩
  intro ε hε σ
  apply Paper3.homogeneousFourierNorm_le_physical hs hs0
    ((scalarProfile_smooth ν hv x₀ T hθ hη i).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))
    (Paper3.compact_spatial_slice (scalarProfile_slice_compact ν hv x₀ T hθ hη hθc hηc i ε) σ)
    hC₁
  · simpa only [pow_one, Function.comp_def, id_eq] using h₁ ε hε σ
  · exact h₂ ε hε σ

/-- The actual homogeneous time norms of the force profiles are uniformly
finite in the scale parameter, not merely finite separately at each scale. -/
theorem scalarProfile_uniform_homogeneous_time (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Icc (0 : ℝ) 1,
      MemLp (fun σ => Source.homogeneousFourierNorm s
        (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z))) q volume ∧
      eLpNorm (fun σ => Source.homogeneousFourierNorm s
        (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z))) q volume ≤ C := by
  obtain ⟨B, hB, hb⟩ := scalarProfile_uniform_homogeneous ν hv x₀ T hθ hη hθc hηc i hs hs0
  let g : ℝ → ℝ := (tsupport η).indicator (fun _ => B)
  have hg : MemLp g q volume := memLp_indicator_const q (isClosed_tsupport η).measurableSet B
    (Or.inr hηc.measure_ne_top)
  refine ⟨eLpNorm g q volume, hg.eLpNorm_lt_top, ?_⟩
  intro ε hε
  refine ⟨Paper3.memLp_homogeneousFourier_time hs hs0
    ((scalarProfile_smooth ν hv x₀ T hθ hη i).comp (contDiff_const.prodMk contDiff_id))
    (scalarProfile_slice_compact ν hv x₀ T hθ hη hθc hηc i ε) q, ?_⟩
  apply eLpNorm_mono_real
  intro σ
  rw [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ Source.homogeneousFourierNorm s _ from Real.sqrt_nonneg _)]
  by_cases hσ : σ ∈ tsupport η
  · simpa only [g, Set.indicator_of_mem hσ] using hb ε hε σ
  · have hz : (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z)) = 0 := by
      funext z
      exact scalarProfile_zero ν hv x₀ T hθ hη i ε (σ, z) (fun h => hσ h.1)
    simp [hz, Source.homogeneousFourierNorm, g, hσ, Real.fourier_eq]

theorem fourierSobolevNorm_smul_nonneg (s : ℝ) (f : Space → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    Source.fourierSobolevNorm s (fun x => a • f x) = a * Source.fourierSobolevNorm s f := by
  have hF (ξ : Space) : 𝓕 (fun x => a • f x) ξ = a • 𝓕 f ξ := by
    simp only [Real.fourier_eq, smul_comm _ a, integral_smul]
  unfold Source.fourierSobolevNorm Source.fourierSobolevSq
  simp_rw [hF, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, mul_pow]
  have he : (∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * (a ^ 2 * ‖𝓕 f ξ‖ ^ 2)) =
      a ^ 2 * ∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  rw [he, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]

def scalarPhysicalForce (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (i : Fin 3) (ε : ℝ) (p : SpaceTime) : ℂ :=
  (Source.correctionForce ν v (physicalCorrection v x₀ T θ η ε) p i : ℂ)

theorem scalarPhysicalForce_eq (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T ε : ℝ) (hε : 0 < ε) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η) (i : Fin 3) (t : ℝ) :
    (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x)) =
      fun x => ε • Source.parabolicComplexForce ε⁻¹ T
        (fun σ z => scalarProfile ν v x₀ T θ η i (ε, σ, z)) t (x - x₀) := by
  funext x
  unfold scalarPhysicalForce
  rw [physicalForce_eq_profile ν hv x₀ T ε hε.ne' hθ hη]
  have ha : ε * (ε ^ 3)⁻¹ = (ε ^ 2)⁻¹ := by field_simp
  simp only [Source.parabolicComplexForce, Source.concentratedForce, scalarProfile,
    smul_smul, inv_pow, inverseScale_apply, Prod.fst_sub, Prod.snd_sub]
  change (((ε ^ 2)⁻¹ *
    forceProfile ν v x₀ T θ η (ε, (ε ^ 2)⁻¹ * (t - T), ε⁻¹ • (x - x₀)) i : ℝ) : ℂ) = _
  simp only [Complex.ofReal_mul, Complex.real_smul]
  have hca := congrArg (fun a : ℝ => (a : ℂ)) ha
  simp only [Complex.ofReal_mul] at hca
  rw [hca]

/-- The actual background correction force has one extra power of ε in its
mixed norm: ε^(2/q - 1/2 - s), with a constant independent of ε. -/
theorem scalarPhysicalForce_uniform_negative_time (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      eLpNorm (fun t => Source.fourierSobolevNorm s
        (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C := by
  obtain ⟨C, hC, hb⟩ := scalarProfile_uniform_homogeneous_time ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  refine ⟨C, hC, ?_⟩
  intro ε hε
  let F : SpaceTime → ℂ := fun z => scalarProfile ν v x₀ T θ η i (ε, z)
  have hF : ContDiff ℝ ∞ F :=
    (scalarProfile_smooth ν hv x₀ T hθ hη i).comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport F := scalarProfile_slice_compact ν hv x₀ T hθ hη hθc hηc i ε
  have hscale := Source.force_eLpNorm_negative_epsilon hs0 hε.1 T q (fun t x => F (t, x))
    (Paper3.compact_spacetime_fourier_slice_continuous hF hc)
    (fun t => Paper3.compact_fourier_homogeneous_negative_integrable hs hs0 _
      (hF.comp (contDiff_const.prodMk contDiff_id)) (Paper3.compact_spatial_slice hc t))
    (Paper3.stronglyMeasurable_homogeneousFourier_time s hF.continuous)
  have heq : (fun t => Source.fourierSobolevNorm s
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) =
      ε • (fun t => Source.fourierSobolevNorm s
        (Source.parabolicComplexForce ε⁻¹ T (fun σ z => F (σ, z)) t)) := by
    funext t
    rw [scalarPhysicalForce_eq ν hv x₀ T ε hε.1 hθ hη i t,
      fourierSobolevNorm_smul_nonneg s _ hε.1.le, Source.fourierSobolevNorm_translate]
    rfl
  rw [heq, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_pos hε.1]
  calc
    _ ≤ ENNReal.ofReal ε * (ENNReal.ofReal (ε ^ (2 / q.toReal - 3 / 2 - s)) * C) := by
      exact mul_le_mul_right (hscale.trans (mul_le_mul_right (hb ε ⟨hε.1.le, hε.2⟩).2 _)) _
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hε.1.le]
      congr 2
      conv_lhs => arg 1; rw [← Real.rpow_one ε]
      rw [← Real.rpow_add hε.1]
      congr 1
      ring

/-- Vanishing of the actual correction-force norm follows from the certified
uniform profile bound and its genuine ε exponent. -/
theorem scalarPhysicalForce_negative_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : -3 / 2 < s) (hs0 : s ≤ 0) (q : ℝ≥0∞)
    (hβ : 0 < 2 / q.toReal - 1 / 2 - s) :
    Filter.Tendsto (fun ε => eLpNorm (fun t => Source.fourierSobolevNorm s
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := scalarPhysicalForce_uniform_negative_time ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  exact Source.ennreal_tendsto_zero_of_power_bound hβ hC.ne
    (fun ε hε hε1 => hb ε ⟨hε, hε1⟩)

end NSFormalization.Paper1.CorrectionForceNorms
