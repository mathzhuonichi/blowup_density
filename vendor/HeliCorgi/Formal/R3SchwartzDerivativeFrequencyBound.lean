import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Formal.R3H3DerivativeWeightGeometry

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/-- The fixed frequency-multiplier constant for the `i`-th coordinate derivative. -/
def r3CoordinateDerivativeFrequencyConstant (i : Fin 3) : ℝ :=
  ‖(2 * Real.pi * Complex.I : ℂ)‖ * ‖r3CoordinateDirection i‖

@[simp]
theorem r3CoordinateDerivativeFrequencyConstant_nonneg (i : Fin 3) :
    0 ≤ r3CoordinateDerivativeFrequencyConstant i := by
  unfold r3CoordinateDerivativeFrequencyConstant
  positivity

/-- Fourier transform of the concrete `i`-th coordinate derivative. -/
theorem fourier_r3SchwartzCoordinateDerivative_eq
    (i : Fin 3) (v : R3SchwartzVelocity) :
    𝓕 (r3SchwartzCoordinateDerivative i v) =
      (2 * Real.pi * Complex.I) •
        SchwartzMap.smulLeftCLM R3C
          (fun ξ : R3 => inner ℝ ξ (r3CoordinateDirection i)) (𝓕 v) := by
  simpa [r3SchwartzCoordinateDerivative] using
    (SchwartzMap.fourier_lineDerivOp_eq v (r3CoordinateDirection i))

/-- Cauchy--Schwarz pointwise bound for the Fourier multiplier of one coordinate derivative. -/
theorem norm_fourier_r3SchwartzCoordinateDerivative_le
    (i : Fin 3) (v : R3SchwartzVelocity) (ξ : R3) :
    ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖ ≤
      ‖(2 * Real.pi * Complex.I : ℂ)‖ *
        ((‖ξ‖ * ‖r3CoordinateDirection i‖) * ‖(𝓕 v) ξ‖) := by
  rw [fourier_r3SchwartzCoordinateDerivative_eq]
  rw [smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), norm_smul, norm_smul]
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right
      (norm_inner_le_norm ξ (r3CoordinateDirection i))
      (norm_nonneg ((𝓕 v) ξ)))
    (norm_nonneg (2 * Real.pi * Complex.I : ℂ))

/-- After order-two weighting, the derivative Fourier field is pointwise dominated by the
order-three frequency coordinate of the undifferentiated field. -/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_coordinateDerivative_le
    (i : Fin 3) (v : R3SchwartzVelocity) (ξ : R3) :
    ‖r3H2WeightedVelocitySchwartz
        (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖ ≤
      r3CoordinateDerivativeFrequencyConstant i *
        ‖r3SchwartzSobolevFrequencyCoordinate 3 v ξ‖ := by
  rw [norm_r3H2WeightedVelocitySchwartz]
  calc
    r3H2BesselWeight ξ * ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) ξ‖ ≤
        r3H2BesselWeight ξ *
          (‖(2 * Real.pi * Complex.I : ℂ)‖ *
            ((‖ξ‖ * ‖r3CoordinateDirection i‖) * ‖(𝓕 v) ξ‖)) :=
      mul_le_mul_of_nonneg_left
        (norm_fourier_r3SchwartzCoordinateDerivative_le i v ξ)
        (le_of_lt (r3H2BesselWeight_pos ξ))
    _ = r3CoordinateDerivativeFrequencyConstant i *
        ((r3H2BesselWeight ξ * ‖ξ‖) * ‖(𝓕 v) ξ‖) := by
      unfold r3CoordinateDerivativeFrequencyConstant
      ring
    _ ≤ r3CoordinateDerivativeFrequencyConstant i *
        (‖r3SobolevWeightComplex 3 ξ‖ * ‖(𝓕 v) ξ‖) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (r3H2BesselWeight_mul_norm_le_H3Weight ξ)
          (norm_nonneg ((𝓕 v) ξ)))
        (r3CoordinateDerivativeFrequencyConstant_nonneg i)
    _ = r3CoordinateDerivativeFrequencyConstant i *
        ‖r3SchwartzSobolevFrequencyCoordinate 3 v ξ‖ := by
      unfold r3SchwartzSobolevFrequencyCoordinate
      rw [SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), norm_smul]
      change
        r3CoordinateDerivativeFrequencyConstant i *
            (‖Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2))‖ * ‖(𝓕 v) ξ‖) =
          r3CoordinateDerivativeFrequencyConstant i *
            (‖Complex.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2))‖ * ‖(𝓕 v) ξ‖)
      rfl

end

end MNS2
