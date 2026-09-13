import NSFormalization.Paper1.CorrectionForceNorms
import NSFormalization.Paper3.PositiveFourierTime

/-! Positive-order uniform force norms from the actual first derivatives. -/
noncomputable section
namespace NSFormalization.Paper1.CorrectionForceNorms
open NavierStokes NavierStokes.ProblemStatement Set MeasureTheory
open CorrectionProfile CorrectionForceProfile CorrectionEnergy
open scoped ContDiff ENNReal FourierTransform

theorem scalarProfile_support (ν : ℝ) (v : VelocityField) (x₀ : Space) (T : ℝ)
    (θ : Space → ℝ) (η : ℝ → ℝ) (i : Fin 3) :
    tsupport (scalarProfile ν v x₀ T θ η i) ⊆ tsupport (forceProfile ν v x₀ T θ η) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_contra hn
  apply hp
  simp [scalarProfile, image_eq_zero_of_notMem_tsupport hn]

theorem scalarProfile_derivative_uniform_energy (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i j : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ,
      (∫ z : Space, ‖NavierStokes.PeriodicIntegration.spatialPartial j
        (fun x => scalarProfile ν v x₀ T θ η i (ε, σ, x)) z‖ ^ 2) ≤ C := by
  let F := scalarProfile ν v x₀ T θ η i
  let D : Parameter → ℂ := fun p => fderiv ℝ F p (spatialInclusion (coordinateVector j))
  have hF : ContDiff ℝ ∞ F := scalarProfile_smooth ν hv x₀ T hθ hη i
  have hD : ContDiff ℝ ∞ D := (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hs (ε : ℝ) (z : SpaceTime) (hz : z ∉ tsupport η ×ˢ tsupport θ) : D (ε, z) = 0 := by
    have hn : (ε, z) ∉ tsupport F := fun h => hz
      ((profile_support hv x₀ T hθ hη
        (forceProfile_support ν v x₀ T θ η (scalarProfile_support ν v x₀ T θ η i h))).2)
    simp only [D, fderiv_of_notMem_tsupport ℝ hn, zero_apply]
  obtain ⟨B, hb⟩ := (isCompact_Icc.prod (hηc.prod hθc)).exists_bound_of_continuousOn hD.continuous.continuousOn
  let B' := max B 0
  have hbound (ε : ℝ) (hε : ε ∈ Icc (0 : ℝ) 1) (z : SpaceTime) : ‖D (ε, z)‖ ≤ B' := by
    by_cases hz : z ∈ tsupport η ×ˢ tsupport θ
    · exact (hb (ε, z) ⟨hε, hz⟩).trans (le_max_left _ _)
    · rw [hs ε z hz, norm_zero]
      exact le_max_right _ _
  refine ⟨volume.real (tsupport θ) * B' ^ 2, by positivity, ?_⟩
  intro ε hε σ
  have heq (z : Space) : NavierStokes.PeriodicIntegration.spatialPartial j
      (fun x => F (ε, σ, x)) z = D (ε, σ, z) := by
    have hin : HasFDerivAt (fun x : Space => (ε, σ, x)) spatialInclusion z :=
      (hasFDerivAt_const (𝕜 := ℝ) ε z).prodMk
        ((hasFDerivAt_const (𝕜 := ℝ) σ z).prodMk (hasFDerivAt_id (𝕜 := ℝ) z))
    have hd := (((hF.differentiable (by simp)) (ε, σ, z)).hasFDerivAt.comp z hin).fderiv
    change fderiv ℝ (fun x => F (ε, σ, x)) z = _ at hd
    rw [NavierStokes.PeriodicIntegration.spatialPartial, hd]
    rfl
  change (∫ z : Space, ‖NavierStokes.PeriodicIntegration.spatialPartial j (fun x => F (ε, σ, x)) z‖ ^ 2) ≤ _
  simp_rw [heq]
  exact compact_energy_bound _ hθc B' (fun z => hbound ε hε (σ, z))
    (fun z hz => hs ε (σ, z) (fun h => hz h.2))

theorem scalarProfile_uniform_positive (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : s ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Icc (0 : ℝ) 1, ∀ σ : ℝ,
      Source.fourierSobolevNorm s (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z)) ≤ C := by
  obtain ⟨C₀, _, h₀⟩ := scalarProfile_uniform_moments ν hv x₀ T hθ hη hθc hηc i 2 (by norm_num)
  have hd (j : Fin 3) := scalarProfile_derivative_uniform_energy ν hv x₀ T hθ hη hθc hηc i j
  choose C hC hb using hd
  refine ⟨Real.sqrt (C₀ + ∑ j, C j), Real.sqrt_nonneg _, ?_⟩
  intro ε hε σ
  exact Paper3.fourierSobolevNorm_le_physical_first hs
    ((scalarProfile_smooth ν hv x₀ T hθ hη i).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)))
    (Paper3.compact_spatial_slice (scalarProfile_slice_compact ν hv x₀ T hθ hη hθc hηc i ε) σ)
    (h₀ ε hε σ) (fun j => hb j ε hε σ)

theorem scalarProfile_uniform_positive_time (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : s ≤ 1) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Icc (0 : ℝ) 1,
      MemLp (fun σ => Source.fourierSobolevNorm s
        (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z))) q volume ∧
      eLpNorm (fun σ => Source.fourierSobolevNorm s
        (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z))) q volume ≤ C := by
  obtain ⟨B, hB, hb⟩ := scalarProfile_uniform_positive ν hv x₀ T hθ hη hθc hηc i hs
  let g : ℝ → ℝ := (tsupport η).indicator (fun _ => B)
  have hg : MemLp g q volume := memLp_indicator_const q (isClosed_tsupport η).measurableSet B
    (Or.inr hηc.measure_ne_top)
  refine ⟨eLpNorm g q volume, hg.eLpNorm_lt_top, ?_⟩
  intro ε hε
  refine ⟨Paper3.memLp_fourierSobolev_le_one_time hs
    ((scalarProfile_smooth ν hv x₀ T hθ hη i).comp (contDiff_const.prodMk contDiff_id))
    (scalarProfile_slice_compact ν hv x₀ T hθ hη hθc hηc i ε) q, ?_⟩
  apply eLpNorm_mono_real
  intro σ
  rw [Real.norm_eq_abs, abs_of_nonneg
    (show 0 ≤ Source.fourierSobolevNorm s _ from Real.sqrt_nonneg _)]
  by_cases hσ : σ ∈ tsupport η
  · simpa only [g, Set.indicator_of_mem hσ] using hb ε hε σ
  · have hz : (fun z => scalarProfile ν v x₀ T θ η i (ε, σ, z)) = 0 := by
      funext z
      exact scalarProfile_zero ν hv x₀ T hθ hη i ε (σ, z) (fun h => hσ h.1)
    simp [hz, Source.fourierSobolevNorm, Source.fourierSobolevSq, g, hσ, Real.fourier_eq]

theorem scalarPhysicalForce_uniform_positive_time (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : s ≤ 1) (hs0 : 0 ≤ s) (q : ℝ≥0∞) :
    ∃ C : ℝ≥0∞, C < (⊤ : ℝ≥0∞) ∧ ∀ ε ∈ Ioc (0 : ℝ) 1,
      eLpNorm (fun t => Source.fourierSobolevNorm s
        (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume ≤
      ENNReal.ofReal (ε ^ (2 / q.toReal - 1 / 2 - s)) * C := by
  obtain ⟨C, hC, hb⟩ := scalarProfile_uniform_positive_time ν hv x₀ T hθ hη hθc hηc i hs q
  refine ⟨C, hC, ?_⟩
  intro ε hε
  let F : SpaceTime → ℂ := fun z => scalarProfile ν v x₀ T θ η i (ε, z)
  have hF : ContDiff ℝ ∞ F :=
    (scalarProfile_smooth ν hv x₀ T hθ hη i).comp (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport F := scalarProfile_slice_compact ν hv x₀ T hθ hη hθc hηc i ε
  have hscale := Source.force_eLpNorm_positive_epsilon hs0 hε.1 hε.2 T q (fun t x => F (t, x))
    (Paper3.compact_spacetime_fourier_slice_continuous hF hc)
    (Paper3.compact_spacetime_bessel_slices s hF hc)
    (Paper3.stronglyMeasurable_fourierSobolev_time s hF.continuous)
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
theorem scalarPhysicalForce_positive_tendsto_zero (ν : ℝ) {v : VelocityField} (hv : ContDiff ℝ ∞ v)
    (x₀ : Space) (T : ℝ) {θ : Space → ℝ} {η : ℝ → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hη : ContDiff ℝ ∞ η)
    (hθc : HasCompactSupport θ) (hηc : HasCompactSupport η) (i : Fin 3)
    {s : ℝ} (hs : s ≤ 1) (hs0 : 0 ≤ s) (q : ℝ≥0∞)
    (hβ : 0 < 2 / q.toReal - 1 / 2 - s) :
    Filter.Tendsto (fun ε => eLpNorm (fun t => Source.fourierSobolevNorm s
      (fun x => scalarPhysicalForce ν v x₀ T θ η i ε (t, x))) q volume)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  obtain ⟨C, hC, hb⟩ := scalarPhysicalForce_uniform_positive_time ν hv x₀ T hθ hη hθc hηc i hs hs0 q
  exact Source.ennreal_tendsto_zero_of_power_bound hβ hC.ne
    (fun ε hε hε1 => hb ε ⟨hε, hε1⟩)

end NSFormalization.Paper1.CorrectionForceNorms
