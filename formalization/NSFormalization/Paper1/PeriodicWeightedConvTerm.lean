import NSFormalization.Paper1.PeriodicPicardBilinear
import NSFormalization.Paper1.PeriodicWeightShift

noncomputable section
namespace NSFormalization.Paper1.PeriodicWeightedConvTerm
open PeriodicPicardBilinear
open scoped BigOperators

def weightedConvTerm (r : ℕ) (f g : FiniteFourier)
    (n l : PeriodicFrequency) : ℝ :=
  Real.sqrt ((periodicFrequencyWeight l) ^ r) * ‖f l‖ *
    (Real.sqrt ((periodicFrequencyWeight (n - l)) ^ r) * ‖g (n - l)‖) ^ 2

theorem weightedConvTerm_nonneg (r : ℕ) (f g : FiniteFourier)
    (n l : PeriodicFrequency) : 0 ≤ weightedConvTerm r f g n l := by
  unfold weightedConvTerm
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (sq_nonneg _)

theorem weightedConvTerm_sum_comm (r : ℕ) (f g : FiniteFourier)
    (K : Finset PeriodicFrequency) :
    (∑ n ∈ K, ∑ l ∈ f.support, weightedConvTerm r f g n l) =
      ∑ l ∈ f.support, ∑ n ∈ K, weightedConvTerm r f g n l := by
  rw [Finset.sum_comm]

end NSFormalization.Paper1.PeriodicWeightedConvTerm
