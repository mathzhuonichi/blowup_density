import Mathlib
namespace NSFormalization.Paper1

theorem sqrt_pow_mul_sq (r : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    (Real.sqrt ((2 : ℝ) ^ r) * A) ^ 2 = (2 : ℝ) ^ r * A ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (by norm_num) r)]

end NSFormalization.Paper1
