import Formal.R3H2AdditiveConvolutionWeight
import Formal.R3H2YoungWeightedBridge
import Formal.R3SchwartzProductConvolution

namespace MNS2

open MeasureTheory FourierTransform

noncomputable section

/--
The additive order-two Bessel split integrated against a scalar--velocity Schwartz convolution
kernel.  The two terms on the right are exactly the `L² * L¹` and `L¹ * L²` Young inputs that will
be bundled in the next step.
-/
theorem r3H2BesselWeight_norm_integral_frequencyKernel_le_additiveWeighted
    (a : R3SchwartzScalar) (b : R3SchwartzVelocity) (ξ : R3) :
    r3H2BesselWeight ξ *
        ‖∫ η : R3, r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
      2 * ∫ η : R3,
        (‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖ +
          ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
  have hw : 0 ≤ r3H2BesselWeight ξ :=
    (r3H2BesselWeight_pos ξ).le
  have hA2shift :
      Integrable (fun η : R3 => ‖r3H2WeightedScalarSchwartz a (ξ - η)‖) := by
    simpa using
      ((r3H2WeightedScalarSchwartz a).integrable.norm.comp_sub_left ξ)
  have hbMeas : AEStronglyMeasurable (fun η : R3 => ‖b η‖) :=
    b.continuous.norm.aestronglyMeasurable
  have hbBound :
      ∀ᵐ η : R3, ‖(‖b η‖ : ℝ)‖ ≤ SchwartzMap.seminorm ℝ 0 0 b := by
    filter_upwards with η
    simpa [Real.norm_of_nonneg (norm_nonneg (b η))] using
      (SchwartzMap.norm_le_seminorm ℝ b η)
  have hleft :
      Integrable (fun η : R3 =>
        ‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖) := by
    exact hA2shift.mul_bdd hbMeas hbBound
  have haShift : Integrable (fun η : R3 => ‖a (ξ - η)‖) := by
    simpa using (a.integrable.norm.comp_sub_left ξ)
  have hB2Meas :
      AEStronglyMeasurable (fun η : R3 => ‖r3H2WeightedVelocitySchwartz b η‖) :=
    (r3H2WeightedVelocitySchwartz b).continuous.norm.aestronglyMeasurable
  have hB2Bound :
      ∀ᵐ η : R3,
        ‖(‖r3H2WeightedVelocitySchwartz b η‖ : ℝ)‖ ≤
          SchwartzMap.seminorm ℝ 0 0 (r3H2WeightedVelocitySchwartz b) := by
    filter_upwards with η
    simpa [Real.norm_of_nonneg (norm_nonneg (r3H2WeightedVelocitySchwartz b η))] using
      (SchwartzMap.norm_le_seminorm ℝ (r3H2WeightedVelocitySchwartz b) η)
  have hright :
      Integrable (fun η : R3 =>
        ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
    exact haShift.mul_bdd hB2Meas hB2Bound
  have hmajor :
      Integrable (fun η : R3 =>
        2 * (‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖ +
          ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖)) := by
    simpa using (hleft.add hright).const_mul 2
  have hpoint : ∀ η : R3,
      r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
        2 * (‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖ +
          ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
    intro η
    calc
      r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
          2 * ((r3H2BesselWeight (ξ - η) * ‖a (ξ - η)‖) * ‖b η‖ +
            ‖a (ξ - η)‖ * (r3H2BesselWeight η * ‖b η‖)) :=
        r3H2BesselWeight_frequencyKernel_le_additive a b ξ η
      _ = 2 * (‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖ +
          ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
        rw [norm_r3H2WeightedScalarSchwartz, norm_r3H2WeightedVelocitySchwartz]
  calc
    r3H2BesselWeight ξ *
        ‖∫ η : R3, r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
        r3H2BesselWeight ξ *
          ∫ η : R3, ‖r3FrequencyScalarVelocityKernel a b ξ η‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_integral_le_integral_norm
          (fun η : R3 => r3FrequencyScalarVelocityKernel a b ξ η)) hw
    _ = ∫ η : R3,
        r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ := by
      rw [integral_const_mul]
    _ ≤ ∫ η : R3,
        2 * (‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖ +
          ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
      exact integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun η =>
          mul_nonneg hw (norm_nonneg (r3FrequencyScalarVelocityKernel a b ξ η)))
        hmajor
        (Filter.Eventually.of_forall hpoint)
    _ = 2 * ∫ η : R3,
        (‖r3H2WeightedScalarSchwartz a (ξ - η)‖ * ‖b η‖ +
          ‖a (ξ - η)‖ * ‖r3H2WeightedVelocitySchwartz b η‖) := by
      rw [integral_const_mul]

/--
One physical convection summand `uᵢ ∂ᵢv`, after the exact product--convolution bridge, satisfies the
additive order-two pointwise frequency majorant.  This is still a pointwise integral estimate; the
`L²` Young bundling needed for `R3SchwartzConvectionTermSobolevEstimate 3` is not claimed here.
-/
theorem norm_r3H2WeightedVelocitySchwartz_fourier_convectionTerm_le_additiveIntegral
    (i : Fin 3) (u v : R3SchwartzVelocity) (ξ : R3) :
    ‖r3H2WeightedVelocitySchwartz (𝓕 (r3SchwartzConvectionTerm i u v)) ξ‖ ≤
      2 * ∫ η : R3,
        (‖r3H2WeightedScalarSchwartz (𝓕 (r3SchwartzCoordinate i u)) (ξ - η)‖ *
            ‖(𝓕 (r3SchwartzCoordinateDerivative i v)) η‖ +
          ‖(𝓕 (r3SchwartzCoordinate i u)) (ξ - η)‖ *
            ‖r3H2WeightedVelocitySchwartz
              (𝓕 (r3SchwartzCoordinateDerivative i v)) η‖) := by
  rw [norm_r3H2WeightedVelocitySchwartz]
  rw [fourier_r3SchwartzConvectionTerm_apply_eq_integral]
  simpa [r3FrequencyScalarVelocityKernel] using
    (r3H2BesselWeight_norm_integral_frequencyKernel_le_additiveWeighted
      (𝓕 (r3SchwartzCoordinate i u))
      (𝓕 (r3SchwartzCoordinateDerivative i v)) ξ)

end

end MNS2
