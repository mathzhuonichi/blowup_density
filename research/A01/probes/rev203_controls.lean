import NSFormalization.Section4.A01.SignedLimit

namespace NSFormalization.Section4.A01

-- The mutation in `rev203_mutation.lean` is mathematically false, not just a
-- syntactic mismatch: these values satisfy the premise and refute `4 * ν ↦ 8 * ν`.
example : (1 : ℝ) * 2 ≤ 2 * 1 * 1 + 0 * 1 ∧
    ¬ (((1 : ℝ) * 2 - 1 * 1 ^ 2) / Real.sqrt (1 ^ 2 + 1 ^ 2) ≤
      2 ^ 2 / (8 * 1) * 1 + 0) := by
  constructor
  · norm_num
  · norm_num only [one_mul, mul_one, zero_mul, add_zero, one_pow, sub_self, pow_two,
      OfNat.ofNat, Nat.cast_ofNat]
    have hs0 : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hs2 : Real.sqrt (2 : ℝ) < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    rw [not_le, div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hs0]
    linarith

end NSFormalization.Section4.A01
