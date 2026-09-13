import Mathlib

namespace NSFormalization.Paper1

open scoped BigOperators

theorem Finset.sum_const_mul (s : Finset α) (c : ℝ) (f : α → ℝ) :
    (∑ x ∈ s, c * f x) = c * ∑ x ∈ s, f x := by
  rw [Finset.mul_sum]

theorem Finset.sum_const_mul_nested (s : Finset α) (t : Finset β)
    (c : ℝ) (f : α → β → ℝ) :
    (∑ x ∈ s, ∑ y ∈ t, c * f x y) = c * ∑ x ∈ s, ∑ y ∈ t, f x y := by
  simp_rw [Finset.sum_const_mul]

end NSFormalization.Paper1

namespace NSFormalization.Paper1
open scoped BigOperators

theorem Finset.const_mul_sum_mem (s : Finset α) (c : ℝ) (f : α → ℝ) :
    c * (∑ x ∈ s, f x) = ∑ x ∈ s, c * f x := by
  simp_rw [Finset.mul_sum]
end NSFormalization.Paper1
