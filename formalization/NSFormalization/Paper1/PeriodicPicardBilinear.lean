import NSFormalization.Paper1.PeriodicHeatMultiplier

noncomputable section
namespace NSFormalization.Paper1.PeriodicPicardBilinear

open NSFormalization.Paper1.PeriodicHeatMultiplier
open scoped BigOperators

abbrev FiniteFourier := Finsupp PeriodicFrequency ℂ

/-- Finite-support convolution coefficient at output frequency `n`.
The sum is restricted to the support of `f`; terms where `g` vanishes are
filtered out. This is an algebraic coefficient map only, with no PDE claim. -/
def convolutionCoeff (f g : FiniteFourier) (n : PeriodicFrequency) : ℂ :=
  Finset.sum (f.support.filter (fun k => g (n - k) ≠ 0))
    (fun k => f k * g (n - k))

@[simp] theorem convolutionCoeff_zero_left (g : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff 0 g n = 0 := by
  simp [convolutionCoeff]

@[simp] theorem convolutionCoeff_zero_right (f : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff f 0 n = 0 := by
  simp [convolutionCoeff]

/-- Terms excluded by the support filter are zero. -/
theorem convolutionCoeff_eq_sum_support (f g : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff f g n = ∑ k ∈ f.support, f k * g (n - k) := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro k hk hnot
  have hz : g (n - k) = 0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hk, hn⟩)
  simp [hz]

/-- Convolution is additive in its second finite-support input. -/
theorem convolutionCoeff_add_right (f g₁ g₂ : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff f (g₁ + g₂) n =
      convolutionCoeff f g₁ n + convolutionCoeff f g₂ n := by
  simp only [convolutionCoeff_eq_sum_support, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

/-- Convolution is additive in its first finite-support input. -/
theorem convolutionCoeff_add_left (f₁ f₂ g : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff (f₁ + f₂) g n =
      convolutionCoeff f₁ g n + convolutionCoeff f₂ g n := by
  simp only [convolutionCoeff_eq_sum_support]
  exact Finsupp.sum_add_index (f := f₁) (g := f₂)
    (h := fun k a => a * g (n - k))
    (fun k _ => zero_mul _) (fun k _ a b => add_mul a b _)

end NSFormalization.Paper1.PeriodicPicardBilinear
