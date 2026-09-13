import Formal.R3H2CoordinateFourierBounds

namespace MNS2

noncomputable section

/-- The norm of the order-three complex Bessel multiplier is the real order-three weight. -/
theorem norm_r3SobolevWeightComplex_three (ξ : R3) :
    ‖r3SobolevWeightComplex 3 ξ‖ =
      (1 + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2) := by
  unfold r3SobolevWeightComplex
  rw [Complex.norm_of_nonneg]
  exact Real.rpow_nonneg (by positivity) _

/-- One frequency factor can be absorbed by raising the Bessel weight from order two to order
three.  This is the scalar geometry behind the quantitative `H³ → H²` derivative estimate. -/
theorem r3H2BesselWeight_mul_norm_le_H3Weight (ξ : R3) :
    r3H2BesselWeight ξ * ‖ξ‖ ≤ ‖r3SobolevWeightComplex 3 ξ‖ := by
  rw [norm_r3SobolevWeightComplex_three]
  unfold r3H2BesselWeight
  have hbase_pos : 0 < (1 : ℝ) + ‖ξ‖ ^ 2 := by positivity
  have hbase_nonneg : 0 ≤ (1 : ℝ) + ‖ξ‖ ^ 2 := hbase_pos.le
  have hsq : ‖ξ‖ ^ 2 ≤ (1 : ℝ) + ‖ξ‖ ^ 2 := by linarith
  have hroot : ‖ξ‖ ≤ √((1 : ℝ) + ‖ξ‖ ^ 2) :=
    Real.le_sqrt_of_sq_le hsq
  have hthree : (3 : ℝ) / 2 = 1 + 1 / 2 := by norm_num
  calc
    ((1 : ℝ) + ‖ξ‖ ^ 2) * ‖ξ‖ ≤
        ((1 : ℝ) + ‖ξ‖ ^ 2) * √((1 : ℝ) + ‖ξ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hroot hbase_nonneg
    _ = ((1 : ℝ) + ‖ξ‖ ^ 2) *
        ((1 : ℝ) + ‖ξ‖ ^ 2) ^ ((1 : ℝ) / 2) := by
      rw [Real.sqrt_eq_rpow]
    _ = ((1 : ℝ) + ‖ξ‖ ^ 2) ^ ((3 : ℝ) / 2) := by
      rw [hthree, Real.rpow_add hbase_pos, Real.rpow_one]

/-- A single Euclidean coordinate frequency factor is likewise absorbed by the order-three Bessel
weight. -/
theorem r3H2BesselWeight_mul_coordinate_norm_le_H3Weight
    (i : Fin 3) (ξ : R3) :
    r3H2BesselWeight ξ * ‖ξ i‖ ≤ ‖r3SobolevWeightComplex 3 ξ‖ := by
  calc
    r3H2BesselWeight ξ * ‖ξ i‖ ≤ r3H2BesselWeight ξ * ‖ξ‖ :=
      mul_le_mul_of_nonneg_left (PiLp.norm_apply_le ξ i)
        (le_of_lt (r3H2BesselWeight_pos ξ))
    _ ≤ ‖r3SobolevWeightComplex 3 ξ‖ :=
      r3H2BesselWeight_mul_norm_le_H3Weight ξ

end

end MNS2
