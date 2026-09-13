import Formal.R3H2BesselWeightGeometry

namespace MNS2

noncomputable section

/-- The order-two Bessel weight is at least one. -/
theorem one_le_r3H2BesselWeight (ξ : R3) :
    1 ≤ r3H2BesselWeight ξ := by
  unfold r3H2BesselWeight
  nlinarith [sq_nonneg ‖ξ‖]

/--
Pointwise frequency kernel for a scalar factor acting on a complexified velocity factor.

This is the bilinear integrand that appears after a physical scalar--velocity product is converted
into a frequency convolution.
-/
def r3FrequencyScalarVelocityKernel
    (a : R3 → ℂ) (b : R3 → R3C) (ξ η : R3) : R3C :=
  a (ξ - η) • b η

/--
Push the output `H²` Bessel weight through one scalar--velocity convolution kernel.

The entire frequency geometry is explicit here:
`⟨ξ⟩² ‖a(ξ-η) b(η)‖` is controlled by the product of the two separately weighted input norms,
with only the factor `2` from `r3H2BesselWeight_le_sub_mul`.
-/
theorem r3H2BesselWeight_norm_smul_le
    (ξ η : R3) (a : ℂ) (b : R3C) :
    r3H2BesselWeight ξ * ‖a • b‖ ≤
      2 * (r3H2BesselWeight (ξ - η) * ‖a‖) *
        (r3H2BesselWeight η * ‖b‖) := by
  have hw := r3H2BesselWeight_le_sub_mul ξ η
  have hn : 0 ≤ ‖a‖ * ‖b‖ :=
    mul_nonneg (norm_nonneg a) (norm_nonneg b)
  calc
    r3H2BesselWeight ξ * ‖a • b‖ =
        r3H2BesselWeight ξ * (‖a‖ * ‖b‖) := by
      rw [norm_smul]
    _ ≤ (2 * r3H2BesselWeight (ξ - η) * r3H2BesselWeight η) *
        (‖a‖ * ‖b‖) := by
      exact mul_le_mul_of_nonneg_right hw hn
    _ = 2 * (r3H2BesselWeight (ξ - η) * ‖a‖) *
        (r3H2BesselWeight η * ‖b‖) := by
      ring

/-- Functional form of the weighted kernel estimate used under the convolution integral. -/
theorem r3H2BesselWeight_frequencyKernel_le
    (a : R3 → ℂ) (b : R3 → R3C) (ξ η : R3) :
    r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
      2 * (r3H2BesselWeight (ξ - η) * ‖a (ξ - η)‖) *
        (r3H2BesselWeight η * ‖b η‖) := by
  exact r3H2BesselWeight_norm_smul_le ξ η (a (ξ - η)) (b η)

/--
Dropping the output weight gives the corresponding unweighted majorization.  This is convenient
when only integrability of the convolution kernel is needed.
-/
theorem norm_r3FrequencyScalarVelocityKernel_le_weighted
    (a : R3 → ℂ) (b : R3 → R3C) (ξ η : R3) :
    ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
      2 * (r3H2BesselWeight (ξ - η) * ‖a (ξ - η)‖) *
        (r3H2BesselWeight η * ‖b η‖) := by
  have hout :
      ‖r3FrequencyScalarVelocityKernel a b ξ η‖ ≤
        r3H2BesselWeight ξ * ‖r3FrequencyScalarVelocityKernel a b ξ η‖ := by
    simpa [one_mul] using
      mul_le_mul_of_nonneg_right (one_le_r3H2BesselWeight ξ)
        (norm_nonneg (r3FrequencyScalarVelocityKernel a b ξ η))
  exact hout.trans (r3H2BesselWeight_frequencyKernel_le a b ξ η)

end

end MNS2
