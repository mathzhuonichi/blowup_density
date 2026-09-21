import NSFormalization.Paper3.HomogeneousTime
import NavierStokes.R3.FourierTestDerivatives

/-! Actual positive-order Fourier time norms, bounded by physical first derivatives. -/
noncomputable section
namespace NSFormalization.Paper3
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NavierStokesR3.HarmonicTestFunctionals
open scoped ContDiff ENNReal

 theorem fourier_coordinate_sq_le (φ : SchwartzMap Space ℂ) (ξ : Space) (i : Fin 3) :
    (ξ i) ^ 2 * ‖𝓕 φ ξ‖ ^ 2 ≤ ‖𝓕 (partialCLM i φ) ξ‖ ^ 2 := by
  have h := fourier_partialCLM_apply i φ ξ
  have hn := congrArg norm h
  change ‖𝓕 (partialCLM i φ) ξ‖ = ‖(2 : ℂ) * ↑Real.pi * Complex.I * ↑(ξ i) * 𝓕 φ ξ‖ at hn
  simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hn
  norm_num at hn
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hmul : |ξ i| * ‖𝓕 φ ξ‖ ≤ ‖𝓕 (partialCLM i φ) ξ‖ := by
    rw [hn]
    nlinarith [mul_nonneg (abs_nonneg (ξ i)) (norm_nonneg (𝓕 φ ξ))]
  have hs := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hmul
  simpa [mul_pow, sq_abs] using hs

 theorem bessel_one_energy_le_physical (φ : SchwartzMap Space ℂ) :
    (∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖𝓕 φ ξ‖ ^ 2) ≤
      (∫ x : Space, ‖φ x‖ ^ 2) + ∑ i : Fin 3, ∫ x : Space, ‖partialCLM i φ x‖ ^ 2 := by
  have hi (ψ : SchwartzMap Space ℂ) : Integrable (fun ξ : Space => ‖𝓕 ψ ξ‖ ^ 2) :=
    ((𝓕 ψ).memLp 2 volume).integrable_norm_pow (by norm_num)
  have hp (ξ : Space) : (1 + ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖𝓕 φ ξ‖ ^ 2 ≤
      ‖𝓕 φ ξ‖ ^ 2 + ∑ i : Fin 3, ‖𝓕 (partialCLM i φ) ξ‖ ^ 2 := by
    have hn : ‖ξ‖ ^ 2 = (ξ 0) ^ 2 + (ξ 1) ^ 2 + (ξ 2) ^ 2 := by
      simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc]
    simp [Real.rpow_one, hn, Fin.sum_univ_succ]
    nlinarith [fourier_coordinate_sq_le φ ξ 0, fourier_coordinate_sq_le φ ξ 1,
      fourier_coordinate_sq_le φ ξ 2]
  have h := integral_mono (schwartz_bessel_integrable 1 (𝓕 φ))
    ((hi φ).add (integrable_finsetSum _ (fun i _ => hi (partialCLM i φ)))) hp
  change (∫ ξ : Space, (1 + ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖𝓕 φ ξ‖ ^ 2) ≤
    ∫ ξ : Space, ‖𝓕 φ ξ‖ ^ 2 + ∑ i : Fin 3, ‖𝓕 (partialCLM i φ) ξ‖ ^ 2 at h
  rw [integral_add (hi φ) (integrable_finsetSum _ (fun i _ => hi (partialCLM i φ))),
    integral_finsetSum _ (fun i _ => hi (partialCLM i φ))] at h
  simpa only [SchwartzMap.integral_norm_sq_fourier] using h

/-- For every order at most one, physical first derivatives bound the actual
inhomogeneous Fourier norm; the constants can be uniform in extra parameters. -/
theorem fourierSobolevNorm_le_physical_first {s C₀ : ℝ} {C : Fin 3 → ℝ}
    (hs : s ≤ 1) {f : Space → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (h₀ : (∫ x : Space, ‖f x‖ ^ 2) ≤ C₀)
    (h₁ : ∀ i, (∫ x : Space, ‖NavierStokes.PeriodicIntegration.spatialPartial i f x‖ ^ 2) ≤ C i) :
    NSFormalization.Source.fourierSobolevNorm s f ≤ Real.sqrt (C₀ + ∑ i, C i) := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  have hmono := integral_besselIntegrand_mono hs (𝓕 φ).continuous
    (schwartz_bessel_integrable 1 (𝓕 φ))
  have hle := bessel_one_energy_le_physical φ
  have hsum : (∫ x : Space, ‖φ x‖ ^ 2) + ∑ i, ∫ x : Space, ‖partialCLM i φ x‖ ^ 2 ≤
      C₀ + ∑ i, C i := add_le_add h₀ (Finset.sum_le_sum (fun i _ => h₁ i))
  exact Real.sqrt_le_sqrt (hmono.trans (hle.trans hsum))

/-- Ambient spacetime derivative in a spatial coordinate direction. -/
def spacetimePartial (i : Fin 3) (F : ℝ × Space → ℂ) (z : ℝ × Space) : ℂ :=
  fderiv ℝ F z (0, coordinateVector i)

 theorem spacetimePartial_smooth {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (i : Fin 3) :
    ContDiff ℝ ∞ (spacetimePartial i F) := by
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

 theorem spacetimePartial_compact {F : ℝ × Space → ℂ} (hc : HasCompactSupport F) (i : Fin 3) :
    HasCompactSupport (spacetimePartial i F) := hc.fderiv_apply ℝ _

 theorem spacetimePartial_eq_slice {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F)
    (i : Fin 3) (t : ℝ) (x : Space) :
    spacetimePartial i F (t, x) =
      NavierStokes.PeriodicIntegration.spatialPartial i (fun y => F (t, y)) x := by
  have h := (hF.differentiable (by simp)).differentiableAt.hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  have heq := h.fderiv
  simp only [Function.comp_def, id_eq] at heq
  rw [NavierStokes.PeriodicIntegration.spatialPartial, heq]
  rfl

/-- All actual inhomogeneous Fourier time norms of order at most one are
uniformly bounded for a compact smooth spacetime input. -/
theorem uniform_fourierSobolev_le_one_time {s : ℝ} (hs : s ≤ 1)
    {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∃ C : ℝ, ∀ t, ‖NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))‖ ≤ C := by
  obtain ⟨C₀, _, h₀⟩ := uniform_integral_norm_pow_time hF.continuous hc 2 (by norm_num)
  have hd (i : Fin 3) := uniform_integral_norm_pow_time
    (spacetimePartial_smooth hF i).continuous (spacetimePartial_compact hc i) 2 (by norm_num)
  choose C hC hbound using hd
  refine ⟨Real.sqrt (C₀ + ∑ i, C i), fun t => ?_⟩
  unfold NSFormalization.Source.fourierSobolevNorm
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply fourierSobolevNorm_le_physical_first hs
    (hF.comp (contDiff_const.prodMk contDiff_id)) (compact_spatial_slice hc t) (h₀ t)
  intro i
  simpa only [spacetimePartial_eq_slice hF, Function.comp_def, id_eq] using hbound i t

/-- Actual time integrability for every time exponent and every inhomogeneous
order at most one, including the positive subcritical L¹ range. -/
theorem memLp_fourierSobolev_le_one_time {s : ℝ} (hs : s ≤ 1)
    {F : ℝ × Space → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (q : ℝ≥0∞) :
    MemLp (fun t => NSFormalization.Source.fourierSobolevNorm s (fun x => F (t, x))) q volume := by
  obtain ⟨C, hC⟩ := uniform_fourierSobolev_le_one_time hs hF hc
  exact (compact_fourierSobolev_time s hc).memLp_of_bound
    (stronglyMeasurable_fourierSobolev_time s hF.continuous).aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

end NSFormalization.Paper3
