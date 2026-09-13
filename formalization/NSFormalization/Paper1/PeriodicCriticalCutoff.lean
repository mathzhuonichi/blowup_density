import NSFormalization.Paper1.PeriodicCriticalBridge

noncomputable section
namespace NSFormalization.Paper1
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open scoped BigOperators ContDiff ENNReal

/-- Inhomogeneous half-order weighted finite energy is monotone under enlarging the cutoff. -/
theorem weightedHalfEnergy_mono {c : PeriodicFrequency → ℂ}
    {S T : Finset PeriodicFrequency} (hST : S ⊆ T) :
    (∑ k ∈ S, periodicFrequencyWeight k ^ (1 / 2 : ℝ) * ‖c k‖ ^ 2) ≤
      ∑ k ∈ T, periodicFrequencyWeight k ^ (1 / 2 : ℝ) * ‖c k‖ ^ 2 := by
  exact Finset.sum_le_sum_of_subset_of_nonneg hST
    (fun k hkT hkS => mul_nonneg
      (Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' zero_le_one) _)
      (sq_nonneg _))

/-- The explicit finite-spectrum cubic bound remains valid after enlarging a cutoff.
This corollary only transports the weighted-energy factor; the inverse-weight
multiplier is retained and no uniform critical embedding is asserted. -/
theorem finite_cubic_bound_of_subset
    (c : PeriodicFrequency → ℂ) {S T : Finset PeriodicFrequency}
    (hST : S ⊆ T) :
    cubeIntegral (fun x => ‖finitePeriodicFourierSum c S x‖ ^ (3 : ℕ)) ≤
      (Real.sqrt (∑ k ∈ T, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) *
        Real.sqrt (∑ k ∈ T, periodicFrequencyWeight k ^ (1 / 2 : ℝ) * ‖c k‖ ^ 2)) ^ (3 : ℕ) := by
  exact (cubeIntegral_norm_fin_fourier_sum_pow_three_le_of_periodicHalfWeight c S).trans
    (by
      have hinv : (∑ k ∈ S, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹) ≤
          ∑ k ∈ T, (periodicFrequencyWeight k ^ (1 / 2 : ℝ))⁻¹ := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun k hkT hkS =>
          inv_nonneg.mpr (le_of_lt (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one
            (one_le_periodicFrequencyWeight k)) _)))
      have hE := weightedHalfEnergy_mono (c := c) hST
      have hmul := mul_le_mul
        (Real.sqrt_le_sqrt hinv) (Real.sqrt_le_sqrt hE)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      exact pow_le_pow_left₀ (by positivity) hmul 3)

end NSFormalization.Paper1
