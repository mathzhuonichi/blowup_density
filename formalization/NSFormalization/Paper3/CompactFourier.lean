import NSFormalization.Paper3.SobolevWeights
import NavierStokes.R3.CompactSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Distribution.Sobolev

/-! Compact smooth functions have the finite negative-order homogeneous Fourier
energy needed by Paper 3. The transform is mathlib's actual Fourier transform;
its exponential uses `2*pi`, as documented by mathlib. -/

noncomputable section
namespace NSFormalization.Paper3
open MeasureTheory FourierTransform NavierStokes.ProblemStatement
open scoped ContDiff

/-- Every Schwartz profile has finite negative-order homogeneous energy in the
valid three-dimensional low-frequency range. -/
theorem schwartz_homogeneous_negative_integrable {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) (φ : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖φ ξ‖ ^ 2) := by
  apply homogeneous_negative_integrable hs hs0 φ.continuous.measurable
    (C := SchwartzMap.seminorm ℝ 0 0 φ)
  · exact apply_nonneg _ _
  · exact SchwartzMap.norm_le_seminorm ℝ φ
  · exact (φ.memLp 2 volume).integrable_norm_pow (by norm_num)

/-- In particular the Fourier transform of a compact smooth scalar function
has finite homogeneous `H^s` squared energy for `-3/2 < s ≤ 0`. -/
theorem compact_fourier_homogeneous_negative_integrable {s : ℝ}
    (hs : -3 / 2 < s) (hs0 : s ≤ 0) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ (2 * s) * ‖𝓕 f ξ‖ ^ 2) := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  exact schwartz_homogeneous_negative_integrable hs hs0 (𝓕 φ)

/-- Every real-order inhomogeneous weighted energy of a Schwartz profile is
finite, by multiplication with the temperate Bessel weight. -/
theorem schwartz_bessel_integrable (s : ℝ) (φ : SchwartzMap Space ℂ) :
    Integrable (besselIntegrand s φ) := by
  let ψ : SchwartzMap Space ℂ := SchwartzMap.smulLeftCLM ℂ
    (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ (s / 2)) φ
  have hψ := (ψ.memLp 2 volume).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have heq (ξ : Space) : ‖ψ ξ‖ ^ 2 = besselIntegrand s φ ξ := by
    rw [show ψ ξ = (1 + ‖ξ‖ ^ 2) ^ (s / 2) • φ ξ from
      SchwartzMap.smulLeftCLM_apply_apply
        (Function.hasTemperateGrowth_one_add_norm_sq_rpow Space (s / 2)) φ ξ]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2)]
    simp only [Nat.cast_ofNat, div_mul_cancel₀ s (by norm_num : (2 : ℝ) ≠ 0)]
    rfl
  simpa only [heq] using hψ

/-- Compact smooth functions have finite actual Fourier `H^s` energy for every
real `s`, including all positive orders. -/
theorem compact_fourier_bessel_integrable (s : ℝ) (f : Space → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Integrable (fun ξ : Space => (1 + ‖ξ‖ ^ 2) ^ s * ‖𝓕 f ξ‖ ^ 2) := by
  let φ := NavierStokesR3.CompactSchwartz.ofCompactSupport f hf hc
  exact schwartz_bessel_integrable s (𝓕 φ)

end NSFormalization.Paper3
