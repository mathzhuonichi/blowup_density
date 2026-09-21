import NSFormalization.Source.RieszFourierProfilePower

noncomputable section
namespace NSFormalization.Source.RieszFourierTestPairing
open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Source.RieszFourierScale
open NSFormalization.Source.RieszFourierProfilePower
open NSFormalization.Source.RieszSchwartzPairing

/-- The frequency power is absolutely integrable against a Schwartz test. -/
theorem power_schwartz_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ (-a) * ‖φ ξ‖) := by
  have h := riesz_schwartz_integrable (a := 3-a) (by linarith) (by linarith) φ
  simpa only [show 3 - a - 3 = -a by ring] using h

/-- Absolute joint integrability of the positive-scale Fourier profiles. -/
theorem profile_schwartz_integrable {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    Integrable (fun p : ℝ × Space => (fourierProfile a p.2 p.1 : ℂ) * φ p.2)
      ((volume.restrict (Ioi 0)).prod volume) := by
  have hm : Measurable (fun p : ℝ × Space => (fourierProfile a p.2 p.1 : ℂ) * φ p.2) := by
    unfold fourierProfile NSFormalization.Source.RieszGaussianMixture.scaleWeight
    fun_prop
  have he (ξ : Space) :
      (fun t : ℝ => ‖(fourierProfile a ξ t : ℂ) * φ ξ‖) =ᵐ[volume.restrict (Ioi 0)]
      (fun t => fourierProfile a ξ t * ‖φ ξ‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (fourierProfile_nonneg ha3 ht ξ)]
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [volume.ae_ne (0 : Space)] with ξ hξ
    exact ((fourierProfile_integrable ha hξ).ofReal.mul_const (φ ξ))
  · apply ((power_schwartz_integrable ha ha3 φ).const_mul (constant a)).congr
    filter_upwards [volume.ae_ne (0 : Space)] with ξ hξ
    rw [integral_congr_ae (he ξ), integral_mul_const, integral_fourierProfile_power ha hξ]
    ring

/-- Exact integrated frequency pairing, justified by absolute Fubini. -/
theorem integral_profile_schwartz {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    (∫ t : ℝ in Ioi 0, ∫ ξ : Space, (fourierProfile a ξ t : ℂ) * φ ξ) =
      ∫ ξ : Space, ((constant a * ‖ξ‖ ^ (-a) : ℝ) : ℂ) * φ ξ := by
  rw [integral_integral_swap (profile_schwartz_integrable ha ha3 φ)]
  apply integral_congr_ae
  filter_upwards [volume.ae_ne (0 : Space)] with ξ hξ
  rw [integral_mul_const, integral_complex_ofReal, integral_fourierProfile_power ha hξ]

/-- The same pairing for the actual individual-scale Fourier transforms. -/
theorem integral_fourier_scale_schwartz {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : SchwartzMap Space ℂ) :
    (∫ t : ℝ in Ioi 0, ∫ ξ : Space,
      FourierTransform.fourier (NSFormalization.Source.RieszGaussianMixture.scaleDensity a t) ξ * φ ξ) =
      ∫ ξ : Space, ((constant a * ‖ξ‖ ^ (-a) : ℝ) : ℂ) * φ ξ := by
  calc
    _ = ∫ t : ℝ in Ioi 0, ∫ ξ : Space, (fourierProfile a ξ t : ℂ) * φ ξ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      apply integral_congr_ae
      filter_upwards with ξ
      rw [NSFormalization.Source.RieszGaussianMixture.fourier_scaleDensity a ht]
      simp only [fourierProfile, Complex.ofReal_mul]
    _ = _ := integral_profile_schwartz ha ha3 φ

end NSFormalization.Source.RieszFourierTestPairing
