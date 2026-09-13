import Mathlib
namespace NSFormalization.Paper1
open scoped BigOperators

theorem finset_triple_weighted_identity
    {α β : Type*} (K : Finset α) (S : Finset β)
    (A : ℝ) (a : β → ℝ) (b : α → β → ℝ) :
    (∑ x ∈ K, A * ∑ y ∈ S, a y * b x y) =
      A * ∑ y ∈ S, a y * ∑ x ∈ K, b x y := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

end NSFormalization.Paper1
