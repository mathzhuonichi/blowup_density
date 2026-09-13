import Mathlib
namespace NSFormalization.Paper1
open scoped BigOperators

theorem finset_weighted_output_rearrange
    {α β : Type*} (K : Finset α) (S : Finset β)
    (A : ℝ) (a : β → ℝ) (F : α → β → ℝ) :
    (∑ n ∈ K, A * ∑ l ∈ S, a l * F n l) =
      A * ∑ l ∈ S, a l * ∑ n ∈ K, F n l := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

end NSFormalization.Paper1
