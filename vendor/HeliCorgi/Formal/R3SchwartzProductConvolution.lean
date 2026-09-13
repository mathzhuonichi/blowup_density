import Mathlib.Analysis.Fourier.Convolution
import Formal.R3SchwartzConvection

namespace MNS2

open MeasureTheory FourierTransform Convolution

noncomputable section

/-- On Schwartz fields over physical `R³`, applying the Fourier transform twice reflects the
spatial argument.  This is the small inversion lemma needed to turn pointwise products into
frequency convolutions without adding a new analytic assumption. -/
theorem r3Schwartz_fourier_fourier_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (f : SchwartzMap R3 F) (ξ : R3) :
    (𝓕 (𝓕 f)) ξ = f (-ξ) := by
  have hξ : (𝓕⁻ (𝓕 f) : SchwartzMap R3 F) (-ξ) = f (-ξ) := by
    simp
  rw [SchwartzMap.fourierInv_apply_eq] at hξ
  simpa using hξ

/-- Exact product--convolution identity on `R³` Schwartz fields for an arbitrary continuous
complex-bilinear fiber map. -/
theorem r3Schwartz_fourier_pairing_eq_convolution
    {F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [CompleteSpace F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [CompleteSpace F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [CompleteSpace F₃]
    (B : F₁ →L[ℂ] F₂ →L[ℂ] F₃)
    (f : SchwartzMap R3 F₁) (g : SchwartzMap R3 F₂) :
    𝓕 (SchwartzMap.pairing B f g) =
      SchwartzMap.convolution B (𝓕 f) (𝓕 g) := by
  have hFourier :
      𝓕 (𝓕 (SchwartzMap.pairing B f g)) =
        𝓕 (SchwartzMap.convolution B (𝓕 f) (𝓕 g)) := by
    ext ξ
    simp [SchwartzMap.fourier_convolution, r3Schwartz_fourier_fourier_apply,
      SchwartzMap.pairing_apply_apply]
  calc
    𝓕 (SchwartzMap.pairing B f g) =
        𝓕⁻ (𝓕 (𝓕 (SchwartzMap.pairing B f g))) := by
      simp
    _ = 𝓕⁻ (𝓕 (SchwartzMap.convolution B (𝓕 f) (𝓕 g))) := by
      rw [hFourier]
    _ = SchwartzMap.convolution B (𝓕 f) (𝓕 g) := by
      simp

/-- The Fourier transform of one physical convection summand `uᵢ ∂ᵢv` is exactly the
scalar--velocity convolution of the two Fourier factors. -/
theorem fourier_r3SchwartzConvectionTerm_eq_convolution
    (i : Fin 3) (u v : R3SchwartzVelocity) :
    𝓕 (r3SchwartzConvectionTerm i u v) =
      SchwartzMap.convolution
        (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C)
        (𝓕 (r3SchwartzCoordinate i u))
        (𝓕 (r3SchwartzCoordinateDerivative i v)) := by
  change
    𝓕 (SchwartzMap.pairing
      (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C)
      (r3SchwartzCoordinate i u)
      (r3SchwartzCoordinateDerivative i v)) = _
  exact r3Schwartz_fourier_pairing_eq_convolution
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C)
    (r3SchwartzCoordinate i u) (r3SchwartzCoordinateDerivative i v)

/-- Pointwise integral form of the exact frequency convolution for one convection summand. -/
theorem fourier_r3SchwartzConvectionTerm_apply_eq_integral
    (i : Fin 3) (u v : R3SchwartzVelocity) (ξ : R3) :
    (𝓕 (r3SchwartzConvectionTerm i u v)) ξ =
      ∫ η : R3,
        (𝓕 (r3SchwartzCoordinate i u)) (ξ - η) •
          (𝓕 (r3SchwartzCoordinateDerivative i v)) η := by
  rw [fourier_r3SchwartzConvectionTerm_eq_convolution]
  rw [SchwartzMap.convolution_apply]
  simpa using
    (MeasureTheory.convolution_eq_swap
      (L := (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] R3C →L[ℂ] R3C))
      (f := fun η : R3 => (𝓕 (r3SchwartzCoordinate i u)) η)
      (g := fun η : R3 => (𝓕 (r3SchwartzCoordinateDerivative i v)) η)
      (μ := (volume : Measure R3))
      (x := ξ))

end

end MNS2
