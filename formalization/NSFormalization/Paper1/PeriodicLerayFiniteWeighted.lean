import NSFormalization.Paper1.PeriodicLerayWeightedNorm

/-! Finite-frequency aggregation of the derivative-weighted Leray bound. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayFiniteWeighted

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicLerayWeightedNorm
open scoped BigOperators

theorem finite_weighted_sum_sq_norm_projectedCoeff_le
    (S : Finset PeriodicFrequency) (g : VectorCoeff) :
    (∑ k ∈ S, periodicFrequencyWeight k *
        (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2)) ≤
      ∑ k ∈ S, periodicFrequencyWeight k *
        (∑ i : Fin 3, ‖g k i‖ ^ 2) := by
  exact Finset.sum_le_sum (fun k hk =>
    weighted_sum_sq_norm_projectedCoeff_le g k)

end NSFormalization.Paper1.PeriodicLerayFiniteWeighted
