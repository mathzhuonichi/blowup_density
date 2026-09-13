import NSFormalization.Paper1.PeriodicWeightShift
import NSFormalization.Paper1.PeriodicPicardBilinear
noncomputable section
namespace NSFormalization.Paper1
open PeriodicPicardBilinear
open scoped BigOperators

def weightedEnergy (r : ℕ) (g : FiniteFourier) : ℝ := ∑ m ∈ g.support, periodicFrequencyWeight m ^ r * ‖g m‖ ^ 2

theorem shifted_weighted_energy_le (r : ℕ) (g : FiniteFourier) (K : Finset PeriodicFrequency) (l : PeriodicFrequency) :
    (∑ n ∈ K, periodicFrequencyWeight (n-l)^r * ‖g (n-l)‖^2) ≤ weightedEnergy r g := by
  classical
  unfold weightedEnergy
  let J := K.image (fun n : PeriodicFrequency => n-l)
  have hi : Set.InjOn (fun n : PeriodicFrequency => n-l) K := by
    intro a ha b hb h
    simpa using congrArg (fun z : PeriodicFrequency => z+l) h
  calc
    _ = ∑ m ∈ J, periodicFrequencyWeight m ^ r * ‖g m‖ ^ 2 := by rw [Finset.sum_image hi]
    _ ≤ ∑ m ∈ J ∪ g.support, periodicFrequencyWeight m ^ r * ‖g m‖ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      intro m hm hn
      exact mul_nonneg (pow_nonneg (zero_le_one.trans (one_le_periodicFrequencyWeight m)) _) (sq_nonneg _)
    _ = _ := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro m hm hn
      simp [Finsupp.notMem_support_iff.mp hn]

end NSFormalization.Paper1
