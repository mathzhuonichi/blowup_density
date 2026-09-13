import Formal.R3H2FourierL1Bound

namespace MNS2

open MeasureTheory FourierTransform
open scoped ENNReal

noncomputable section

/-- Multiplying an order-two weighted velocity Schwartz field by the inverse weight recovers it. -/
theorem r3H2InverseBesselWeightComplex_smul_weightedVelocity
    (b : R3SchwartzVelocity) (ξ : R3) :
    r3H2InverseBesselWeightComplex ξ • r3H2WeightedVelocitySchwartz b ξ = b ξ := by
  rw [r3H2WeightedVelocitySchwartz,
    SchwartzMap.smulLeftCLM_apply_apply (r3SobolevWeightComplex_hasTemperateGrowth 2)]
  rw [smul_smul, r3H2InverseBesselWeightComplex_mul_weight_two]
  simp

/-- The vector-valued `L¹` reconstruction obtained from the inverse `H²` weight and weighted `L²`. -/
def r3H2VelocityL1Reconstruction (b : R3SchwartzVelocity) :
    Lp R3C 1 (volume : Measure R3) :=
  r3H2InverseBesselWeightL2 •
    (r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3)

/-- The vector-valued `L¹` reconstruction agrees almost everywhere with the original field. -/
theorem r3H2VelocityL1Reconstruction_ae (b : R3SchwartzVelocity) :
    r3H2VelocityL1Reconstruction b =ᵐ[volume] b := by
  unfold r3H2VelocityL1Reconstruction
  filter_upwards [
    r3H2InverseBesselWeightL2_ae,
    (r3H2WeightedVelocitySchwartz b).coeFn_toLp 2 (volume : Measure R3),
    Lp.coeFn_lpSMul (r := (1 : ℝ≥0∞)) r3H2InverseBesselWeightL2
      ((r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3))]
    with ξ hinv hweight hsmul
  rw [hsmul, Pi.smul_apply', hinv, hweight]
  exact r3H2InverseBesselWeightComplex_smul_weightedVelocity b ξ

/-- Cauchy--Schwarz in `Lp` form for the vector-valued inverse-weight reconstruction. -/
theorem norm_r3H2VelocityL1Reconstruction_le (b : R3SchwartzVelocity) :
    ‖r3H2VelocityL1Reconstruction b‖ ≤
      ‖r3H2InverseBesselWeightL2‖ *
        ‖(r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3)‖ := by
  unfold r3H2VelocityL1Reconstruction
  exact Lp.norm_smul_le _ _

/-- Quantitative three-dimensional vector-valued `L¹` bound at Sobolev order two. -/
theorem integral_norm_r3SchwartzVelocity_le_H2WeightedL2
    (b : R3SchwartzVelocity) :
    (∫ ξ : R3, ‖b ξ‖) ≤
      ‖r3H2InverseBesselWeightL2‖ *
        ‖(r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3)‖ := by
  have hb : Integrable (fun ξ : R3 => b ξ) := b.integrable
  have hL1 : hb.toL1 (fun ξ : R3 => b ξ) = r3H2VelocityL1Reconstruction b := by
    apply Lp.ext
    filter_upwards [hb.coeFn_toL1, r3H2VelocityL1Reconstruction_ae b] with ξ hleft hright
    rw [hleft, hright]
  calc
    (∫ ξ : R3, ‖b ξ‖) = ‖hb.toL1 (fun ξ : R3 => b ξ)‖ :=
      (L1.norm_of_fun_eq_integral_norm hb).symm
    _ = ‖r3H2VelocityL1Reconstruction b‖ := by rw [hL1]
    _ ≤ ‖r3H2InverseBesselWeightL2‖ *
        ‖(r3H2WeightedVelocitySchwartz b).toLp 2 (volume : Measure R3)‖ :=
      norm_r3H2VelocityL1Reconstruction_le b

/-- The unweighted Fourier `L¹` norm of an `R³` Schwartz velocity is controlled by its H³ norm. -/
theorem integral_norm_fourier_r3SchwartzVelocity_le_H3
    (f : R3SchwartzVelocity) :
    (∫ ξ : R3, ‖(𝓕 f) ξ‖) ≤
      ‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 f‖ := by
  calc
    (∫ ξ : R3, ‖(𝓕 f) ξ‖) ≤
        ‖r3H2InverseBesselWeightL2‖ *
          ‖(r3H2WeightedVelocitySchwartz (𝓕 f)).toLp 2 (volume : Measure R3)‖ :=
      integral_norm_r3SchwartzVelocity_le_H2WeightedL2 (𝓕 f)
    _ ≤ ‖r3H2InverseBesselWeightL2‖ * ‖r3SchwartzToHsCLM 3 f‖ := by
      exact mul_le_mul_of_nonneg_left
        (norm_r3H2WeightedVelocitySchwartz_fourier_toLp_le_H3 f)
        (norm_nonneg r3H2InverseBesselWeightL2)

end

end MNS2
