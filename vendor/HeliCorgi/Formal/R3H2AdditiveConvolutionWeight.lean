import Formal.R3H2WeightedConvolutionKernel

namespace MNS2

noncomputable section

/--
For the `m = 3` product estimate, the order-two output weight is split additively between the two
convolution inputs.  This is the useful form for an `L² * L¹ + L¹ * L²` Young argument.
-/
theorem r3H2BesselWeight_le_additive_split (ξ η : R3) :
    r3H2BesselWeight ξ ≤
      2 * r3H2BesselWeight (ξ - η) + 2 * r3H2BesselWeight η := by
  have htri : ‖ξ‖ ≤ ‖ξ - η‖ + ‖η‖ := by
    calc
      ‖ξ‖ = ‖(ξ - η) + η‖ := by rw [sub_add_cancel]
      _ ≤ ‖ξ - η‖ + ‖η‖ := norm_add_le _ _
  have hgap :
      0 ≤ (‖ξ - η‖ + ‖η‖) - ‖ξ‖ :=
    sub_nonneg.mpr htri
  have hplus :
      0 ≤ (‖ξ - η‖ + ‖η‖) + ‖ξ‖ :=
    add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hsquare :
      ‖ξ‖ ^ 2 ≤ (‖ξ - η‖ + ‖η‖) ^ 2 := by
    have hprod :
        0 ≤ ((‖ξ - η‖ + ‖η‖) - ‖ξ‖) *
          ((‖ξ - η‖ + ‖η‖) + ‖ξ‖) :=
      mul_nonneg hgap hplus
    nlinarith
  have hcross : 0 ≤ (‖ξ - η‖ - ‖η‖) ^ 2 := sq_nonneg _
  unfold r3H2BesselWeight
  nlinarith

/--
Additive weighted estimate for one scalar--velocity convolution kernel.  Only one input carries the
full order-two weight in each summand, which is the structure needed for the three-dimensional
`H²` algebra estimate.
-/
theorem r3H2BesselWeight_norm_smul_le_additive
    (ξ η : R3) (a : ℂ) (b : R3C) :
    r3H2BesselWeight ξ * ‖a • b‖ ≤
      2 * ((r3H2BesselWeight (ξ - η) * ‖a‖) * ‖b‖ +
        ‖a‖ * (r3H2BesselWeight η * ‖b‖)) := by
  have hw := r3H2BesselWeight_le_additive_split ξ η
  have hn : 0 ≤ ‖a‖ * ‖b‖ :=
    mul_nonneg (norm_nonneg a) (norm_nonneg b)
  calc
    r3H2BesselWeight ξ * ‖a • b‖ =
        r3H2BesselWeight ξ * (‖a‖ * ‖b‖) := by
      rw [norm_smul]
    _ ≤ (2 * r3H2BesselWeight (ξ - η) + 2 * r3H2BesselWeight η) *
        (‖a‖ * ‖b‖) := by
      exact mul_le_mul_of_nonneg_right hw hn
    _ = 2 * ((r3H2BesselWeight (ξ - η) * ‖a‖) * ‖b‖ +
        ‖a‖ * (r3H2BesselWeight η * ‖b‖)) := by
      ring

/-- Functional form of the additive weighted kernel estimate used under the convolution integral. -/
theorem r3H2BesselWeight_frequencyKernel_le_additive
    (a : R3 → ℂ) (b : R3 → R3C) (ξ η : R3) :
    r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
      2 * ((r3H2BesselWeight (ξ - η) * ‖a (ξ - η)‖) * ‖b η‖ +
        ‖a (ξ - η)‖ * (r3H2BesselWeight η * ‖b η‖)) := by
  exact r3H2BesselWeight_norm_smul_le_additive ξ η (a (ξ - η)) (b η)

end

end MNS2
