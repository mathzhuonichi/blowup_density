import NSFormalization.Paper1.PeriodicLerayFiniteWeighted

/-! Finite-frequency Leray estimate for arbitrary nonnegative real weights. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayHighWeight

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicLerayNorm
open scoped BigOperators

theorem high_weight_nonneg (s : ℝ) (hs : 0 ≤ s) (k : PeriodicFrequency) :
    0 ≤ periodicFrequencyWeight k ^ s := by
  exact Real.rpow_nonneg ((one_le_periodicFrequencyWeight k).trans' (by norm_num)) s

theorem finite_high_weight_sum_sq_norm_projectedCoeff_le
    (S : Finset PeriodicFrequency) (s : ℝ) (hs : 0 ≤ s)
    (g : VectorCoeff) :
    (∑ k ∈ S, periodicFrequencyWeight k ^ s *
        (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2)) ≤
      ∑ k ∈ S, periodicFrequencyWeight k ^ s *
        (∑ i : Fin 3, ‖g k i‖ ^ 2) := by
  exact Finset.sum_le_sum (fun k hk =>
    mul_le_mul_of_nonneg_left (sum_sq_norm_projectedCoeff_le g k)
      (high_weight_nonneg s hs k))

end NSFormalization.Paper1.PeriodicLerayHighWeight
