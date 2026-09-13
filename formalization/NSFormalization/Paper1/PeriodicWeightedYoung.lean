import NSFormalization.Paper1.PeriodicWeightedOutputIntermediate
import NSFormalization.Paper1.PeriodicShiftedWeightedEnergy
import NSFormalization.Paper1.FinsetWeightedOutputRearrange

/-! # Weighted discrete Young inequality on the native periodic lattice

Finite Fourier inputs and arbitrary finite output sets satisfy a bound with
constant depending only on the natural Sobolev weight exponent. No support
cardinality or PDE existence hypothesis enters the estimate.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicWeightedYoung
open PeriodicPicardBilinear PeriodicWeightedCoeffBound
open scoped BigOperators

theorem weighted_convolution_energy_le (r : ℕ) (f g : FiniteFourier)
    (K : Finset PeriodicFrequency) :
    (∑ n ∈ K, periodicFrequencyWeight n ^ r * ‖convolutionCoeff f g n‖ ^ 2) ≤
      (2 : ℝ) ^ r *
        (∑ l ∈ f.support, Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖) ^ 2 *
        weightedEnergy r g := by
  let a : PeriodicFrequency → ℝ := fun l =>
    Real.sqrt (periodicFrequencyWeight l ^ r) * ‖f l‖
  let A : ℝ := ∑ l ∈ f.support, a l
  have ha (l : PeriodicFrequency) : 0 ≤ a l :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun l _ => ha l)
  have hC : 0 ≤ (2 : ℝ) ^ r * A := mul_nonneg (by positivity) hA
  have hshift (l : PeriodicFrequency) :
      (∑ n ∈ K, (Real.sqrt (periodicFrequencyWeight (n-l)^r) * ‖g (n-l)‖)^2)
        ≤ weightedEnergy r g := by
    simpa only [mul_pow, Real.sq_sqrt (pow_nonneg
      (zero_le_one.trans (one_le_periodicFrequencyWeight _)) r)] using
      shifted_weighted_energy_le r g K l
  calc
    _ ≤ ∑ n ∈ K, ((2 : ℝ)^r * A) *
        ∑ l ∈ f.support, a l *
          (Real.sqrt (periodicFrequencyWeight (n-l)^r) * ‖g (n-l)‖)^2 :=
      weighted_output_intermediate_le r f g K
    _ = ((2 : ℝ)^r * A) * ∑ l ∈ f.support, a l *
        ∑ n ∈ K, (Real.sqrt (periodicFrequencyWeight (n-l)^r) * ‖g (n-l)‖)^2 :=
      finset_weighted_output_rearrange K f.support _ a _
    _ ≤ ((2 : ℝ)^r * A) * ∑ l ∈ f.support, a l * weightedEnergy r g := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hshift l) (ha l))
    _ = _ := by
      rw [← Finset.sum_mul]
      change (2 : ℝ)^r * A * (A * weightedEnergy r g) =
        (2 : ℝ)^r * A^2 * weightedEnergy r g
      ring

end NSFormalization.Paper1.PeriodicWeightedYoung
