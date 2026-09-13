import Mathlib
namespace NSFormalization.Paper1

theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (h : a ≤ b) : a ^ 2 ≤ b ^ 2 := by
  nlinarith [mul_self_nonneg (b - a)]

theorem sqrt_mul_norm_sq {w z : ℝ} (hw : 0 ≤ w) :
    (Real.sqrt w * ‖z‖) ^ 2 = w * ‖z‖ ^ 2 := by
  rw [mul_pow, Real.sq_sqrt hw]

end NSFormalization.Paper1
