import NSFormalization.Paper1.PeriodicLerayNorm

/-! Derivative-weighted, frequencywise Leray energy bound. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayWeightedNorm

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicLerayNorm

theorem frequency_weight_nonneg (k : PeriodicFrequency) :
    0 ≤ periodicFrequencyWeight k :=
  (one_le_periodicFrequencyWeight k).trans' (by norm_num)

/-- Multiplying the Euclidean Leray estimate by the nonnegative derivative
weight preserves the inequality at each frequency. -/
theorem weighted_sum_sq_norm_projectedCoeff_le
    (g : VectorCoeff) (k : PeriodicFrequency) :
    periodicFrequencyWeight k *
        (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2) ≤
      periodicFrequencyWeight k * (∑ i : Fin 3, ‖g k i‖ ^ 2) := by
  exact mul_le_mul_of_nonneg_left
    (sum_sq_norm_projectedCoeff_le g k) (frequency_weight_nonneg k)

end NSFormalization.Paper1.PeriodicLerayWeightedNorm
