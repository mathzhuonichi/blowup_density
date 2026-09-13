import Mathlib
namespace NSFormalization.Paper1
open scoped BigOperators

theorem weighted_finset_cauchy_schwarz
    {α : Type*} (s : Finset α) (a b : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤
      (∑ i ∈ s, a i) * ∑ i ∈ s, a i * b i ^ 2 := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun i hi => ha i hi)
    (fun i hi => mul_nonneg (ha i hi) (sq_nonneg _))
    (fun i hi => by nlinarith [sq_nonneg (a i * b i)])

end NSFormalization.Paper1

namespace NSFormalization.Paper1
open scoped BigOperators

theorem weighted_nested_sum_swap
    {α β : Type*} (s : Finset α) (t : Finset β)
    (a : β → ℝ) (b : α → β → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, a y * b x y) =
      ∑ y ∈ t, a y * ∑ x ∈ s, b x y := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.mul_sum]
end NSFormalization.Paper1
