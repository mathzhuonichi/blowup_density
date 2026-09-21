import NSFormalization.Source.RieszKernelFourier
import NSFormalization.Source.RieszSingularMultiplier

/-! Exact conventional Riesz kernel normalization in the cycles Fourier convention. -/
noncomputable section
namespace NSFormalization.Source.RieszKernelNormalization
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped SchwartzMap

/-- Conventional physical convolution coefficient in dimension three. -/
def coefficient (a : ℝ) : ℝ :=
  Real.Gamma ((3-a)/2) / (2 ^ a * Real.pi ^ (3/2 : ℝ) * Real.Gamma (a/2))

theorem coefficient_pos {a : ℝ} (ha : 0 < a) (ha3 : a < 3) : 0 < coefficient a := by
  unfold coefficient
  have h1 := Real.Gamma_pos_of_pos (show 0 < (3-a)/2 by linarith)
  have h2 := Real.Gamma_pos_of_pos (show 0 < a/2 by linarith)
  positivity

/-- The full Gamma/pi factors reduce to the cycles-frequency symbol factor. -/
theorem coefficient_mul_constant {a : ℝ} (ha : 0 < a) (ha3 : a < 3) :
    coefficient a * RieszFourierProfilePower.constant a = (2 * Real.pi) ^ (-a) := by
  have h1 := (Real.Gamma_pos_of_pos (show 0 < (3-a)/2 by linarith)).ne'
  have h2 := (Real.Gamma_pos_of_pos (show 0 < a/2 by linarith)).ne'
  have ht : (2 : ℝ) ^ a ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) a).ne'
  have hp : Real.pi ^ (3/2 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  have hpa : Real.pi ^ a ≠ 0 := (Real.rpow_pos_of_pos Real.pi_pos _).ne'
  unfold coefficient RieszFourierProfilePower.constant
  rw [Real.rpow_sub Real.pi_pos,
    Real.rpow_neg (mul_nonneg (by norm_num) Real.pi_pos.le),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) Real.pi_pos.le]
  field_simp

/-- The normalized physical kernel has the exact cycles Fourier symbol
on every Schwartz test. This is not yet a convolution theorem for L2 inputs. -/
theorem normalized_kernel_fourier_pairing {a : ℝ} (ha : 0 < a) (ha3 : a < 3)
    (φ : 𝓢(Space, ℂ)) :
    (∫ x : Space, (coefficient a : ℂ) * (‖x‖ ^ (a-3) : ℝ) * (𝓕 φ) x) =
      ∫ ξ : Space, Complex.ofReal (Real.rpow (2 * Real.pi) (-a)) *
        (‖ξ‖ ^ (-a) : ℝ) * φ ξ := by
  simp_rw [mul_assoc (coefficient a : ℂ)]
  rw [integral_const_mul, RieszKernelFourier.kernel_fourier_pairing ha ha3,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  have he : (coefficient a : ℂ) * RieszFourierProfilePower.constant a =
      Complex.ofReal (Real.rpow (2 * Real.pi) (-a)) := by
    rw [← Complex.ofReal_mul, coefficient_mul_constant ha ha3]
    rfl
  push_cast
  calc
    _ = ((coefficient a : ℂ) * RieszFourierProfilePower.constant a) *
        (‖ξ‖ ^ (-a) : ℝ) * φ ξ := by ring
    _ = _ := by rw [he]

end NSFormalization.Source.RieszKernelNormalization
