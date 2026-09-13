import NSFormalization.Source.RieszGaussianMixture
import NSFormalization.Source.RieszSchwartzPairing
import NSFormalization.Source.RieszFourierTestPairing

/-! Fourier duality for the Riesz Gaussian scales. The Gaussian is L1 and the
other factor is Schwartz, so Mathlib's ordinary Fourier integral theorem applies. -/
noncomputable section
namespace NSFormalization.Source.RieszKernelFourier
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.Source.RieszGaussianMixture
open scoped SchwartzMap

theorem scale_fourier_duality (a : ℝ) {t : ℝ} (ht : 0 < t) (φ : 𝓢(Space, ℂ)) :
    (∫ ξ : Space, 𝓕 (scaleDensity a t) ξ * φ ξ) =
      ∫ x : Space, scaleDensity a t x * (𝓕 φ) x := by
  simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ Space)
    Real.continuous_fourierChar continuous_inner
    (scaleDensity_integrable a ht) φ.integrable

/-- The Fourier transform of the full Riesz power kernel, in exact
Schwartz pairing and with the cycles-frequency Gamma/pi constant. -/
theorem kernel_fourier_pairing {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : 𝓢(Space, ℂ)) :
    (∫ x : Space, ((‖x‖ ^ (a-3) : ℝ) : ℂ) * (𝓕 φ) x) =
      ∫ ξ : Space,
        ((RieszFourierProfilePower.constant a * ‖ξ‖ ^ (-a) : ℝ) : ℂ) * φ ξ := by
  rw [← RieszSchwartzPairing.integral_scale_schwartz ha ha3 (𝓕 φ),
    ← RieszFourierTestPairing.integral_profile_schwartz ha ha3 φ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [← scale_fourier_duality a ht φ]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [fourier_scaleDensity a ht]
  simp only [RieszFourierScale.fourierProfile, Complex.ofReal_mul]

end NSFormalization.Source.RieszKernelFourier
