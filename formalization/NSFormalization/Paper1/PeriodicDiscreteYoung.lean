import NSFormalization.Paper1.PeriodicPicardBilinear

/-!
# Constant-one discrete Young inequality

The output is summed over an arbitrary finite set, while both input norms use
all nonzero coefficients. No support cardinality enters the bound.
-/
noncomputable section
namespace NSFormalization.Paper1.PeriodicDiscreteYoung

open PeriodicPicardBilinear
open scoped BigOperators

/-- Translation of a finite output set cannot increase the total input energy. -/
theorem shifted_energy_le (g : FiniteFourier) (K : Finset PeriodicFrequency)
    (l : PeriodicFrequency) :
    (∑ n ∈ K, ‖g (n - l)‖ ^ 2) ≤ ∑ m ∈ g.support, ‖g m‖ ^ 2 := by
  classical
  let J := K.image (fun n => n - l)
  have hinj : Set.InjOn (fun n : PeriodicFrequency => n - l) K := by
    intro a ha b hb hab
    simpa using congrArg (fun x : PeriodicFrequency => x + l) hab
  calc
    (∑ n ∈ K, ‖g (n - l)‖ ^ 2) = ∑ m ∈ J, ‖g m‖ ^ 2 := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑ m ∈ J ∪ g.support, ‖g m‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro m hm hnot
      exact sq_nonneg _
    _ = ∑ m ∈ g.support, ‖g m‖ ^ 2 := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro m hm hnot
      simp [Finsupp.notMem_support_iff.mp hnot]

/-- Weighted Cauchy–Schwarz at one output coefficient, with weight `‖f l‖`. -/
theorem convolutionCoeff_sq_le (f g : FiniteFourier) (n : PeriodicFrequency) :
    ‖convolutionCoeff f g n‖ ^ 2 ≤
      (∑ l ∈ f.support, ‖f l‖) *
        ∑ l ∈ f.support, ‖f l‖ * ‖g (n - l)‖ ^ 2 := by
  have htriangle : ‖convolutionCoeff f g n‖ ≤
      ∑ l ∈ f.support, ‖f l‖ * ‖g (n - l)‖ := by
    rw [convolutionCoeff_eq_sum_support]
    simpa only [norm_mul] using norm_sum_le f.support (fun l => f l * g (n - l))
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul f.support
    (r := fun l => ‖f l‖ * ‖g (n - l)‖)
    (f := fun l => ‖f l‖)
    (g := fun l => ‖f l‖ * ‖g (n - l)‖ ^ 2)
    (fun l _ => norm_nonneg (f l))
    (fun l _ => mul_nonneg (norm_nonneg _) (sq_nonneg _))
    (fun l _ => by nlinarith [sq_nonneg (‖f l‖ * ‖g (n - l)‖)])
  exact (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans hcs

/-- Discrete `ℓ¹ * ℓ² → ℓ²` Young inequality in squared form, with constant one. -/
theorem convolution_energy_le (f g : FiniteFourier) (K : Finset PeriodicFrequency) :
    (∑ n ∈ K, ‖convolutionCoeff f g n‖ ^ 2) ≤
      (∑ l ∈ f.support, ‖f l‖) ^ 2 * ∑ m ∈ g.support, ‖g m‖ ^ 2 := by
  have hA : 0 ≤ ∑ l ∈ f.support, ‖f l‖ := Finset.sum_nonneg (fun l _ => norm_nonneg _)
  calc
    (∑ n ∈ K, ‖convolutionCoeff f g n‖ ^ 2) ≤
        ∑ n ∈ K, (∑ l ∈ f.support, ‖f l‖) *
          ∑ l ∈ f.support, ‖f l‖ * ‖g (n - l)‖ ^ 2 := by
      exact Finset.sum_le_sum (fun n _ => convolutionCoeff_sq_le f g n)
    _ = (∑ l ∈ f.support, ‖f l‖) *
        ∑ l ∈ f.support, ‖f l‖ * ∑ n ∈ K, ‖g (n - l)‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp_rw [← Finset.mul_sum]
    _ ≤ (∑ l ∈ f.support, ‖f l‖) *
        ∑ l ∈ f.support, ‖f l‖ * ∑ m ∈ g.support, ‖g m‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_left (shifted_energy_le g K l) (norm_nonneg _)
    _ = (∑ l ∈ f.support, ‖f l‖) ^ 2 * ∑ m ∈ g.support, ‖g m‖ ^ 2 := by
      rw [← Finset.sum_mul]
      ring

end NSFormalization.Paper1.PeriodicDiscreteYoung
