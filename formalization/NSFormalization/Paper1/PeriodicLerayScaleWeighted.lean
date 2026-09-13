import NSFormalization.Paper1.PeriodicLerayFrequencyScale
import NSFormalization.Paper1.PeriodicLerayArbitraryWeight

noncomputable section
namespace NSFormalization.Paper1.PeriodicLerayScaleWeighted

open NSFormalization.Paper1.PeriodicLerayCoeffCore
open NSFormalization.Paper1.PeriodicLerayDivergence
open NSFormalization.Paper1.PeriodicLerayFrequencyScale
open NSFormalization.Paper1.PeriodicLerayArbitraryWeight
open NSFormalization.Paper1.PeriodicLerayNorm
open scoped BigOperators

theorem finite_scaled_projected_energy_le
    (S : Finset PeriodicFrequency) (w : PeriodicFrequency → ℝ)
    (hw : ∀ k, 0 ≤ w k) (g : VectorCoeff) :
    (∑ k ∈ S, ∑ i : Fin 3, ‖frequencyScale w (fun k j => projectedCoeff g j k) k i‖ ^ 2) ≤
      ∑ k ∈ S, w k ^ 2 * (∑ i : Fin 3, ‖g k i‖ ^ 2) := by
  apply Finset.sum_le_sum
  intro k hk
  rw [show (∑ i : Fin 3, ‖frequencyScale w (fun k j => projectedCoeff g j k) k i‖ ^ 2) =
      w k ^ 2 * (∑ i : Fin 3, ‖projectedCoeff g i k‖ ^ 2) by
        simp [frequencyScale, norm_mul, Real.norm_eq_abs, sq_abs, mul_pow,
          Finset.mul_sum]]
  exact mul_le_mul_of_nonneg_left (sum_sq_norm_projectedCoeff_le g k)
    (sq_nonneg (w k))

end NSFormalization.Paper1.PeriodicLerayScaleWeighted
