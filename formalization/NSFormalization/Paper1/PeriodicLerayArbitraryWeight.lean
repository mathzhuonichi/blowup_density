import NSFormalization.Paper1.PeriodicLerayNorm

/-! Finite Leray energy bounds for arbitrary nonnegative frequency weights. -/
noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayArbitraryWeight

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicLerayNorm
open scoped BigOperators

theorem finite_arbitrary_weight_sum_sq_norm_projectedCoeff_le
    (S : Finset PeriodicFrequency) (w : PeriodicFrequency → ℝ)
    (hw : ∀ k, 0 ≤ w k) (g : VectorCoeff) :
    (∑ k ∈ S, w k * (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2)) ≤
      ∑ k ∈ S, w k * (∑ i : Fin 3, ‖g k i‖ ^ 2) := by
  exact Finset.sum_le_sum (fun k hk =>
    mul_le_mul_of_nonneg_left (sum_sq_norm_projectedCoeff_le g k) (hw k))

end NSFormalization.Paper1.PeriodicLerayArbitraryWeight
