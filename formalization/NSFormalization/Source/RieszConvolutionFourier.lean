import NSFormalization.Source.RieszConvolutionFubini
import NSFormalization.Source.RieszSchwartzCorrelation
import NSFormalization.Source.RieszKernelFourier
import NSFormalization.Source.RieszComplexPotential

/-! Actual physical Riesz convolution in Fourier pairing for Schwartz inputs. -/
noncomputable section
namespace NSFormalization.Source.RieszConvolutionFourier
open Set MeasureTheory FourierTransform NavierStokes.ProblemStatement
open NSFormalization.RieszComplexPotential
open scoped SchwartzMap
abbrev Space := NavierStokes.ProblemStatement.Space

theorem schwartz_potential_fourier_pairing {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (g φ : 𝓢(Space, ℂ)) :
    (∫ x : Space, complexPotential a g x * (𝓕 φ) x) =
      ∫ ξ : Space, ((RieszFourierProfilePower.constant a * ‖ξ‖ ^ (-a) : ℝ) : ℂ) *
        ((𝓕 g) ξ * φ ξ) := by
  have htranslate (y : Space) :
      (∫ x : Space, g (x-y) * (𝓕 φ) x) = ∫ z : Space, g z * (𝓕 φ) (y+z) := by
    simpa only [add_sub_cancel_left] using
      (integral_add_left_eq_self (μ := (volume : Measure Space)) (fun x : Space => g (x-y) * (𝓕 φ) x) y).symm
  simp only [complexPotential, Complex.real_smul]
  simp_rw [← integral_mul_const]
  rw [integral_integral_swap (RieszConvolutionFubini.kernel_convolution_test_integrable ha ha3 g (𝓕 φ))]
  simp_rw [mul_assoc, integral_const_mul, htranslate,
    ← RieszSchwartzCorrelation.fourier_pairing_eq_integral]
  exact RieszKernelFourier.kernel_fourier_pairing ha ha3
    (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g) φ)

end NSFormalization.Source.RieszConvolutionFourier
