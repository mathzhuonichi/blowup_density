import Formal.R3SchwartzConvectionSobolevReduction

namespace MNS2

noncomputable section

/-- The real Bessel weight for Sobolev order `2`: `⟨ξ⟩² = 1 + ‖ξ‖²`. -/
def r3H2BesselWeight (ξ : R3) : ℝ :=
  1 + ‖ξ‖ ^ 2

@[simp]
theorem r3H2BesselWeight_pos (ξ : R3) :
    0 < r3H2BesselWeight ξ := by
  unfold r3H2BesselWeight
  positivity

/--
The order-two Bessel weight is submultiplicative up to the explicit factor `2`.

This is the frequency geometry needed when the physical product is converted to convolution:
`⟨ξ + η⟩² ≤ 2 ⟨ξ⟩² ⟨η⟩²`.
-/
theorem r3H2BesselWeight_add_le (ξ η : R3) :
    r3H2BesselWeight (ξ + η) ≤
      2 * r3H2BesselWeight ξ * r3H2BesselWeight η := by
  have htri : ‖ξ + η‖ ≤ ‖ξ‖ + ‖η‖ := norm_add_le ξ η
  have hsum_nonneg : 0 ≤ ‖ξ‖ + ‖η‖ :=
    add_nonneg (norm_nonneg ξ) (norm_nonneg η)
  have hdiff_nonneg : 0 ≤ (‖ξ‖ + ‖η‖) - ‖ξ + η‖ :=
    sub_nonneg.mpr htri
  have hsquare_compare :
      0 ≤ ((‖ξ‖ + ‖η‖) - ‖ξ + η‖) *
        ((‖ξ‖ + ‖η‖) + ‖ξ + η‖) :=
    mul_nonneg hdiff_nonneg (add_nonneg hsum_nonneg (norm_nonneg (ξ + η)))
  have hcross : 0 ≤ (‖ξ‖ - ‖η‖) ^ 2 := sq_nonneg (‖ξ‖ - ‖η‖)
  have hquartic : 0 ≤ (‖ξ‖ * ‖η‖) ^ 2 := sq_nonneg (‖ξ‖ * ‖η‖)
  unfold r3H2BesselWeight
  nlinarith

/-- Convolution form of the order-two Bessel weight inequality. -/
theorem r3H2BesselWeight_le_sub_mul (ξ η : R3) :
    r3H2BesselWeight ξ ≤
      2 * r3H2BesselWeight (ξ - η) * r3H2BesselWeight η := by
  simpa using r3H2BesselWeight_add_le (ξ - η) η

/-- Symmetric convolution form, convenient when the weighted factor is placed on `η`. -/
theorem r3H2BesselWeight_le_mul_sub (ξ η : R3) :
    r3H2BesselWeight ξ ≤
      2 * r3H2BesselWeight η * r3H2BesselWeight (ξ - η) := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    r3H2BesselWeight_le_sub_mul ξ η

end

end MNS2
