import NSFormalization.Paper1.PeriodicWeightedCoeffBound
import NSFormalization.Paper1.NonnegSquareHelpers
import NSFormalization.Paper1.WeightedFinsetCS
import NSFormalization.Paper1.SqrtPowIdentity
noncomputable section
namespace NSFormalization.Paper1.PeriodicWeightedCoeffBound
open PeriodicPicardBilinear PeriodicWeightHalfPower
open scoped BigOperators
 theorem weighted_convolutionCoeff_sq_le (r : ℕ) (f g : FiniteFourier) (n : PeriodicFrequency) :
    periodicFrequencyWeight n ^ r * ‖convolutionCoeff f g n‖ ^ 2 ≤
      (2 : ℝ) ^ r * (∑ l ∈ f.support, Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) *
        ∑ l ∈ f.support, (Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) *
          (Real.sqrt (periodicFrequencyWeight (n-l) ^ r) * ‖g (n-l)‖) ^ 2 := by
  have h := weighted_convolutionCoeff_le r f g n
  have hsq := sq_le_sq_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) h
  have hcs := weighted_finset_cauchy_schwarz f.support
    (fun l : PeriodicFrequency => Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖)
    (fun l : PeriodicFrequency => Real.sqrt (periodicFrequencyWeight (n-l) ^ r) * ‖g (n-l)‖)
    (fun l hl => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg (f l)))
  have hw : 0 ≤ periodicFrequencyWeight n ^ r := pow_nonneg (zero_le_one.trans (one_le_periodicFrequencyWeight n)) _
  rw [mul_pow, Real.sq_sqrt hw] at hsq
  have hA : 0 ≤ ∑ l ∈ f.support, Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖ :=
    Finset.sum_nonneg (fun l _ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hsqR : (Real.sqrt ((2 : ℝ)^r) * (∑ l ∈ f.support, (Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) * (Real.sqrt (periodicFrequencyWeight (n-l) ^ r) * ‖g (n-l)‖)))^2 =
      (2:ℝ)^r * (∑ l ∈ f.support, (Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) * (Real.sqrt (periodicFrequencyWeight (n-l) ^ r) * ‖g (n-l)‖))^2 := by
    rw [mul_pow, Real.sq_sqrt (pow_nonneg (by norm_num) r)]
  rw [hsqR] at hsq
  have hmul := mul_le_mul_of_nonneg_left hcs (pow_nonneg (by norm_num) r : 0 ≤ (2 : ℝ)^r)
  exact hsq.trans (by simpa [mul_assoc] using hmul)
end NSFormalization.Paper1.PeriodicWeightedCoeffBound
