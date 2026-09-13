import NavierStokes.R3RieszKernel
import Mathlib.Analysis.Fourier.Convolution

noncomputable section

namespace NSFormalization.Source.RieszSchwartzCorrelation

open MeasureTheory FourierTransform NavierStokes.ProblemStatement

/-- The Fourier transform of a Schwartz product is the physical correlation. -/
theorem fourier_pairing_eq_integral (g φ : SchwartzMap Space ℂ) (y : Space) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g) φ) y =
      ∫ z : Space, g z * (𝓕 φ) (y + z) := by
  let C := SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g (𝓕⁻ φ)
  have hC : 𝓕 C = SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g) φ := by
    simp [C, SchwartzMap.fourier_convolution]
  have hinv : (𝓕 (𝓕 C)) y = C (-y) := by
    have hi : (𝓕⁻ (𝓕 C : SchwartzMap Space ℂ) : SchwartzMap Space ℂ) = C :=
      fourierInv_fourier_eq C
    have h := congrArg (fun f : SchwartzMap Space ℂ => f (-y)) hi
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_neg,
      ← SchwartzMap.fourier_coe] at h
    exact h
  rw [← hC, hinv, SchwartzMap.convolution_apply, convolution_def]
  apply integral_congr_ae
  filter_upwards with z
  simp [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg,
    ← SchwartzMap.fourier_coe, neg_sub, add_comm]

end NSFormalization.Source.RieszSchwartzCorrelation
