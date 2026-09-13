import NSFormalization.Paper1.PeriodicWeightShift

/-! Half-power frequency-weight estimates for discrete Sobolev convolution.
The constants are independent of the support or frequency cutoff. -/
namespace NSFormalization.Paper1.PeriodicWeightHalfPower

open NSFormalization.Paper1.PeriodicWeightShift

/-- The integer weight-shift estimate at the square-root level. -/
theorem sqrt_shift (k l : PeriodicFrequency) (r : ℕ) :
    Real.sqrt (periodicFrequencyWeight k ^ r) ≤
      Real.sqrt ((2 : ℝ) ^ r) * Real.sqrt (periodicFrequencyWeight l ^ r) *
        Real.sqrt (periodicFrequencyWeight (k - l) ^ r) := by
  have h := Real.sqrt_le_sqrt (weight_shift_pow_le k l r)
  have htwo : 0 ≤ (2 : ℝ) ^ r := pow_nonneg (by norm_num) r
  have hl : 0 ≤ periodicFrequencyWeight l ^ r :=
    pow_nonneg (zero_le_one.trans (one_le_periodicFrequencyWeight l)) r
  rwa [Real.sqrt_mul (mul_nonneg htwo hl), Real.sqrt_mul htwo] at h

/-- Square roots of integer Sobolev weights are exactly the half-order real
powers, with no rounding or change of Fourier normalization. -/
theorem sqrt_weight_pow_eq_rpow (k : PeriodicFrequency) (r : ℕ) :
    Real.sqrt (periodicFrequencyWeight k ^ r) =
      periodicFrequencyWeight k ^ ((r : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul
    (zero_le_one.trans (one_le_periodicFrequencyWeight k))]
  congr 1
  ring

/-- The half-order weight-shift estimate in the native real-power notation. -/
theorem half_power_shift (k l : PeriodicFrequency) (r : ℕ) :
    periodicFrequencyWeight k ^ ((r : ℝ) / 2) ≤
      Real.sqrt ((2 : ℝ) ^ r) * periodicFrequencyWeight l ^ ((r : ℝ) / 2) *
        periodicFrequencyWeight (k - l) ^ ((r : ℝ) / 2) := by
  simpa only [sqrt_weight_pow_eq_rpow] using sqrt_shift k l r

end NSFormalization.Paper1.PeriodicWeightHalfPower
