import Formal.R3YoungL1L2Bochner
import Formal.R3SchwartzSobolevMonotonicity

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/-- Order-two Bessel weighting of a scalar Schwartz frequency field. -/
def r3H2WeightedScalarSchwartz (a : R3SchwartzScalar) : R3SchwartzScalar :=
  SchwartzMap.smulLeftCLM ℂ (r3SobolevWeightComplex 2) a

/-- Order-two Bessel weighting of a velocity Schwartz frequency field. -/
def r3H2WeightedVelocitySchwartz (b : R3SchwartzVelocity) : R3SchwartzVelocity :=
  SchwartzMap.smulLeftCLM R3C (r3SobolevWeightComplex 2) b

/-- At order two, the Sobolev weight norm is exactly the real polynomial Bessel weight. -/
theorem norm_r3SobolevWeightComplex_two (ξ : R3) :
    ‖r3SobolevWeightComplex 2 ξ‖ = r3H2BesselWeight ξ := by
  unfold r3SobolevWeightComplex r3H2BesselWeight
  have htwo : (2 : ℝ) / 2 = 1 := by norm_num
  rw [htwo, Real.rpow_one, Complex.norm_real, Real.norm_of_nonneg]
  positivity

/-- Pointwise norm of the order-two weighted scalar Schwartz field. -/
theorem norm_r3H2WeightedScalarSchwartz
    (a : R3SchwartzScalar) (ξ : R3) :
    ‖r3H2WeightedScalarSchwartz a ξ‖ =
      r3H2BesselWeight ξ * ‖a ξ‖ := by
  rw [r3H2WeightedScalarSchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (r3SobolevWeightComplex_hasTemperateGrowth 2),
    norm_smul, norm_r3SobolevWeightComplex_two]

/-- Pointwise norm of the order-two weighted velocity Schwartz field. -/
theorem norm_r3H2WeightedVelocitySchwartz
    (b : R3SchwartzVelocity) (ξ : R3) :
    ‖r3H2WeightedVelocitySchwartz b ξ‖ =
      r3H2BesselWeight ξ * ‖b ξ‖ := by
  rw [r3H2WeightedVelocitySchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (r3SobolevWeightComplex_hasTemperateGrowth 2),
    norm_smul, norm_r3SobolevWeightComplex_two]

/--
The weighted kernel bound from `R3H2WeightedConvolutionKernel` written directly in terms of the
weighted Schwartz inputs that will be fed to the Young convolution theorem.
-/
theorem r3H2BesselWeight_frequencyKernel_le_weightedSchwartz
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ η : R3) :
    r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
      2 * ‖r3H2WeightedScalarSchwartz a (ξ - η)‖ *
        ‖r3H2WeightedVelocitySchwartz b η‖ := by
  calc
    r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
        2 * (r3H2BesselWeight (ξ - η) * ‖a (ξ - η)‖) *
          (r3H2BesselWeight η * ‖b η‖) :=
      r3H2BesselWeight_frequencyKernel_le a b ξ η
    _ = 2 * ‖r3H2WeightedScalarSchwartz a (ξ - η)‖ *
        ‖r3H2WeightedVelocitySchwartz b η‖ := by
      rw [norm_r3H2WeightedScalarSchwartz, norm_r3H2WeightedVelocitySchwartz]

/-- The weighted velocity field of a Fourier-transformed Schwartz field is the canonical H²
frequency coordinate introduced in the Sobolev monotonicity bridge. -/
theorem r3H2WeightedVelocitySchwartz_fourier_eq_frequencyCoordinate
    (f : R3SchwartzVelocity) :
    r3H2WeightedVelocitySchwartz (𝓕 f) =
      r3SchwartzSobolevFrequencyCoordinate 2 f := by
  rfl

/-- The L² norm of the weighted Fourier velocity field is controlled by the canonical H³ norm. -/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_toLp_le_H3
    (f : R3SchwartzVelocity) :
    ‖(r3H2WeightedVelocitySchwartz (𝓕 f)).toLp 2 (volume : Measure R3)‖ ≤
      ‖r3SchwartzToHsCLM 3 f‖ := by
  rw [r3H2WeightedVelocitySchwartz_fourier_eq_frequencyCoordinate]
  calc
    ‖(r3SchwartzSobolevFrequencyCoordinate 2 f).toLp 2 (volume : Measure R3)‖ =
        ‖r3SchwartzToHsCLM 2 f‖ :=
      (norm_r3SchwartzToHsCLM_eq_frequencyCoordinate 2 f).symm
    _ ≤ ‖r3SchwartzToHsCLM 3 f‖ :=
      norm_r3SchwartzToHsCLM_two_le_three f

/--
Young's inequality applied to the exact order-two weighted scalar/velocity inputs, with the vector
L² factor already upgraded from H² to H³ by the monotonicity bridge.
-/
theorem norm_r3H2WeightedYoungConvolution_fourier_le_H3
    (a : R3SchwartzScalar) (f : R3SchwartzVelocity) :
    ‖r3YoungConvolutionL2 (r3H2WeightedScalarSchwartz a)
        ((r3H2WeightedVelocitySchwartz (𝓕 f)).toLp 2 (volume : Measure R3))‖ ≤
      (∫ ξ : R3, ‖r3H2WeightedScalarSchwartz a ξ‖) *
        ‖r3SchwartzToHsCLM 3 f‖ := by
  have hI : 0 ≤ ∫ ξ : R3, ‖r3H2WeightedScalarSchwartz a ξ‖ := by
    exact integral_nonneg (fun ξ => norm_nonneg (r3H2WeightedScalarSchwartz a ξ))
  calc
    ‖r3YoungConvolutionL2 (r3H2WeightedScalarSchwartz a)
        ((r3H2WeightedVelocitySchwartz (𝓕 f)).toLp 2 (volume : Measure R3))‖ ≤
        (∫ ξ : R3, ‖r3H2WeightedScalarSchwartz a ξ‖) *
          ‖(r3H2WeightedVelocitySchwartz (𝓕 f)).toLp 2 (volume : Measure R3)‖ :=
      norm_r3YoungConvolutionL2_le _ _
    _ ≤ (∫ ξ : R3, ‖r3H2WeightedScalarSchwartz a ξ‖) *
        ‖r3SchwartzToHsCLM 3 f‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_r3H2WeightedVelocitySchwartz_fourier_toLp_le_H3 f) hI

end

end MNS2
