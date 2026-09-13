import NSFormalization.Paper1.PeriodicWeightHalfPower
import NSFormalization.Paper1.PeriodicFinitePicardCoeffBound
import NSFormalization.Paper1.NestedFinsetRearrangement
noncomputable section
namespace NSFormalization.Paper1.PeriodicWeightedCoeffBound
open PeriodicPicardBilinear PeriodicWeightHalfPower
open scoped BigOperators
 theorem weighted_convolutionCoeff_le (r : ℕ) (f g : FiniteFourier) (n : PeriodicFrequency) :
    Real.sqrt (periodicFrequencyWeight n ^ r) * ‖convolutionCoeff f g n‖ ≤
      Real.sqrt ((2 : ℝ) ^ r) * ∑ l ∈ f.support,
        (Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) *
          (Real.sqrt (periodicFrequencyWeight (n - l) ^ r) * ‖g (n - l)‖) := by
  have htri : ‖convolutionCoeff f g n‖ ≤ ∑ l ∈ f.support, ‖f l‖ * ‖g (n-l)‖ := by
    rw [convolutionCoeff_eq_sum_support]
    simpa only [norm_mul] using norm_sum_le f.support (fun l : PeriodicFrequency => f l * g (n-l))
  have hsum := Finset.const_mul_sum_mem f.support
    (Real.sqrt (periodicFrequencyWeight n ^ r))
    (fun l : PeriodicFrequency => ‖f l‖ * ‖g (n-l)‖)
  calc
    _ ≤ Real.sqrt (periodicFrequencyWeight n ^ r) * (∑ l ∈ f.support, ‖f l‖ * ‖g (n-l)‖) := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg _)
    _ = ∑ l ∈ f.support, Real.sqrt (periodicFrequencyWeight n ^ r) * (‖f l‖ * ‖g (n-l)‖) := hsum
    _ ≤ _ := by
      rw [Finset.const_mul_sum_mem]
      apply Finset.sum_le_sum
      intro l hl
      have hs := sqrt_shift n l r
      have hnon : 0 ≤ ‖f l‖ * ‖g (n - l)‖ := mul_nonneg (norm_nonneg (f l)) (norm_nonneg (g (n - l)))
      have hterm := mul_le_mul_of_nonneg_right hs hnon
      convert hterm using 1 <;> ring
end NSFormalization.Paper1.PeriodicWeightedCoeffBound
