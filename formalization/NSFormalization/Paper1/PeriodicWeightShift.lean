import NSFormalization.Paper1.PeriodicSobolevHilbert

/-! # Cutoff-independent shifted frequency weights
These estimates use the native integer lattice and unit-periodic derivative
normalization. They provide weight arithmetic for discrete convolution.
-/
namespace NSFormalization.Paper1.PeriodicWeightShift
open scoped BigOperators

private theorem square_sum_add_le (k l : PeriodicFrequency) :
    (∑ i : Fin 3, ((k + l) i : ℝ) ^ 2) ≤
      2 * ((∑ i : Fin 3, (k i : ℝ) ^ 2) + ∑ i : Fin 3, (l i : ℝ) ^ 2) := by
  calc
    _ ≤ ∑ i : Fin 3, (2 * ((k i : ℝ)^2 + (l i : ℝ)^2)) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Pi.add_apply, Int.cast_add]
      nlinarith [sq_nonneg ((k i : ℝ) - (l i : ℝ))]
    _ = _ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      congr 1 <;> rw [← Finset.mul_sum]
      <;> ring

theorem weight_add_le (k l : PeriodicFrequency) :
    periodicFrequencyWeight (k + l) ≤
      2 * (periodicFrequencyWeight k + periodicFrequencyWeight l - 1) := by
  have h := mul_le_mul_of_nonneg_left (square_sum_add_le k l)
    (sq_nonneg (2 * Real.pi))
  simp only [periodicFrequencyWeight_eq]
  nlinarith

theorem weight_add_le_mul (k l : PeriodicFrequency) :
    periodicFrequencyWeight (k + l) ≤
      2 * periodicFrequencyWeight k * periodicFrequencyWeight l := by
  have hk := one_le_periodicFrequencyWeight k
  have hl := one_le_periodicFrequencyWeight l
  have hprod := mul_nonneg (sub_nonneg.mpr hk) (sub_nonneg.mpr hl)
  nlinarith [weight_add_le k l]

theorem weight_shift_le (k l : PeriodicFrequency) :
    periodicFrequencyWeight k ≤
      2 * periodicFrequencyWeight l * periodicFrequencyWeight (k - l) := by
  simpa only [add_sub_cancel] using weight_add_le_mul l (k - l)

theorem weight_shift_pow_le (k l : PeriodicFrequency) (n : ℕ) :
    periodicFrequencyWeight k ^ n ≤
      2 ^ n * periodicFrequencyWeight l ^ n * periodicFrequencyWeight (k - l) ^ n := by
  have h := pow_le_pow_left₀
    (zero_le_one.trans (one_le_periodicFrequencyWeight k)) (weight_shift_le k l) n
  simpa only [mul_pow] using h

end NSFormalization.Paper1.PeriodicWeightShift
