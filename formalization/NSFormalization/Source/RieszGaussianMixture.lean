import NavierStokes.R3RieszKernel

/-! The actual unnormalized Riesz kernel as an integrable Gaussian scale mixture.
This reuses OpenAI's Gaussian and Gamma-moment APIs. It does not interchange
an infinite scale integral with the Fourier transform of a non-L1 kernel. -/
noncomputable section
namespace NSFormalization.Source.RieszGaussianMixture
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NavierStokes.R3GaussianPressure NavierStokes.R3RieszKernel

/-- Scale weight for the unnormalized kernel |x|^(a-3). -/
def scaleWeight (a t : ℝ) : ℝ :=
  (Real.Gamma ((3 - a) / 2))⁻¹ * t ^ ((3 - a) / 2 - 1)

def scaleDensity (a t : ℝ) (x : Space) : ℂ :=
  (scaleWeight a t : ℂ) * gaussian t x

/-- Actual scale integrability holds away from the spatial origin. -/
theorem scale_integrable {a : ℝ} (ha : a < 3) {x : Space} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => scaleWeight a t * gaussianReal t x) (Ioi 0) := by
  have h := (gamma_moment_integrable (q := (3 - a) / 2 - 1)
    (norm_pos_iff.mpr hx) (by linarith)).const_mul (Real.Gamma ((3 - a) / 2))⁻¹
  simpa only [IntegrableOn, scaleWeight, gaussianReal, mul_assoc] using h

/-- Exact scalar power-kernel representation with its Gamma factor. -/
theorem integral_scaleDensity_real {a : ℝ} (ha : a < 3) {x : Space} (hx : x ≠ 0) :
    (∫ t : ℝ in Ioi 0, scaleWeight a t * gaussianReal t x) = ‖x‖ ^ (a - 3) := by
  have hb : 0 < (3 - a) / 2 := by linarith
  have hG : Real.Gamma ((3 - a) / 2) ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hΓ := Real.integral_rpow_mul_exp_neg_mul_Ioi hb
    (sq_pos_of_pos (norm_pos_iff.mpr hx))
  have he (t : ℝ) : scaleWeight a t * gaussianReal t x =
      (Real.Gamma ((3 - a) / 2))⁻¹ *
        (t ^ ((3 - a) / 2 - 1) * Real.exp (-(‖x‖ ^ 2 * t))) := by
    simp only [scaleWeight, gaussianReal, neg_mul]
    ring_nf
  simp_rw [he]
  rw [integral_const_mul, hΓ, inverse_radius_power (norm_pos_iff.mpr hx)]
  rw [show -2 * ((3 - a) / 2) = a - 3 by ring]
  field_simp

/-- Every positive-scale kernel is an actual L1 function. -/
theorem scaleDensity_integrable (a : ℝ) {t : ℝ} (ht : 0 < t) :
    Integrable (scaleDensity a t) :=
  (gaussian_integrable ht).const_mul _

/-- The exact Fourier transform at each positive Gaussian scale. This uses
OpenAI's Gaussian formula and Mathlib's integral scalar multiplication. -/
theorem fourier_scaleDensity (a : ℝ) {t : ℝ} (ht : 0 < t) (ξ : Space) :
    𝓕 (scaleDensity a t) ξ = (scaleWeight a t : ℂ) *
      (((Real.pi / t) ^ (3 / 2 : ℝ) *
        Real.exp (-(Real.pi ^ 2) * ‖ξ‖ ^ 2 / t) : ℝ) : ℂ) := by
  have hlin : 𝓕 (scaleDensity a t) ξ =
      (scaleWeight a t : ℂ) * 𝓕 (gaussian t) ξ := by
    simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, scaleDensity]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [hlin, fourier_gaussian ht]

/-- Positive finite scale windows give genuine integrable kernels. -/
theorem scaleDensity_integrable_product (a : ℝ) {lo hi : ℝ} (hlo : 0 < lo) :
    Integrable (fun p : ℝ × Space => scaleDensity a p.1 p.2)
      ((volume.restrict (Icc lo hi)).prod volume) := by
  have hw : ContinuousOn (scaleWeight a) (Icc lo hi) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    exact Or.inl (ne_of_gt (hlo.trans_le ht.1))
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have henv : Integrable (fun p : ℝ × Space => C * gaussianReal lo p.2)
      ((volume.restrict (Icc lo hi)).prod volume) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : ℝ => (1 : ℝ))
        (volume.restrict (Icc lo hi))).mul_prod ((gaussianReal_integrable hlo).const_mul C)
  have hm : Measurable (fun p : ℝ × Space => scaleDensity a p.1 p.2) := by
    unfold scaleDensity scaleWeight gaussian gaussianReal
    fun_prop
  apply henv.mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)] with p hp
  have hexp : gaussianReal p.1 p.2 ≤ gaussianReal lo p.2 := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hp.1) (sq_nonneg _)
  have hnorm : ‖scaleDensity a p.1 p.2‖ = ‖scaleWeight a p.1‖ * gaussianReal p.1 p.2 := by
    simp only [scaleDensity, gaussian, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (gaussianReal_pos p.1 p.2)]
  rw [hnorm]
  exact mul_le_mul (hC p.1 hp) hexp (gaussianReal_pos p.1 p.2).le
    ((norm_nonneg _).trans (hC p.1 hp))

/-- An L1 finite-window Gaussian mixture, before any infinite-scale limit. -/
def intervalMixture (a lo hi : ℝ) (x : Space) : ℂ :=
  ∫ t : ℝ in Icc lo hi, scaleDensity a t x

theorem intervalMixture_integrable (a : ℝ) {lo hi : ℝ} (hlo : 0 < lo) :
    Integrable (intervalMixture a lo hi) :=
  (scaleDensity_integrable_product a hlo).integral_prod_right

/-- The finite-window Fourier interchange follows from the proved product
integrability, using the source Riesz-kernel Fubini argument. -/
theorem fourier_intervalMixture (a : ℝ) {lo hi : ℝ} (hlo : 0 < lo) (ξ : Space) :
    𝓕 (intervalMixture a lo hi) ξ =
      ∫ t : ℝ in Icc lo hi, 𝓕 (scaleDensity a t) ξ := by
  let c (x : Space) : ℂ := Real.fourierChar (-inner ℝ x ξ)
  have hm : Measurable c := by unfold c; fun_prop
  have hc (x : Space) : ‖c x‖ = 1 := Circle.norm_coe _
  have hd : Measurable (fun p : ℝ × Space => scaleDensity a p.1 p.2) := by
    unfold scaleDensity scaleWeight gaussian gaussianReal
    fun_prop
  have ht : Integrable (fun p : ℝ × Space => c p.2 * scaleDensity a p.1 p.2)
      ((volume.restrict (Icc lo hi)).prod volume) := by
    apply (scaleDensity_integrable_product a hlo).mono
      ((hm.comp measurable_snd).mul hd).aestronglyMeasurable
    filter_upwards with p
    change ‖c p.2 * scaleDensity a p.1 p.2‖ ≤ ‖scaleDensity a p.1 p.2‖
    simp only [norm_mul, hc, one_mul, le_refl]
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul, intervalMixture]
  simp_rw [← integral_const_mul]
  exact integral_integral_swap ht.swap

/-- Explicit finite-scale multiplier, with the source cycles-frequency constants. -/
theorem fourier_intervalMixture_formula (a : ℝ) {lo hi : ℝ} (hlo : 0 < lo)
    (ξ : Space) :
    𝓕 (intervalMixture a lo hi) ξ = ∫ t : ℝ in Icc lo hi,
      (scaleWeight a t : ℂ) * (((Real.pi / t) ^ (3 / 2 : ℝ) *
        Real.exp (-(Real.pi ^ 2) * ‖ξ‖ ^ 2 / t) : ℝ) : ℂ) := by
  rw [fourier_intervalMixture a hlo]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  exact fourier_scaleDensity a (hlo.trans_le ht.1) ξ

end NSFormalization.Source.RieszGaussianMixture
