import NSFormalization.Paper1.PeriodicPicardBilinear

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardSupport

open NSFormalization.Paper1.PeriodicPicardBilinear

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

/-- A coefficient outside the paired support contributes zero to convolution. -/
theorem convolutionCoeff_eq_zero_of_pairwise_vanish
    (f g : FiniteFourier) (n : PeriodicFrequency)
    (hvanish : ∀ k, f k ≠ 0 → g (n - k) = 0) :
    convolutionCoeff f g n = 0 := by
  classical
  unfold convolutionCoeff
  apply Finset.sum_eq_zero
  intro k hk
  have hkfmem : k ∈ f.support := (Finset.mem_filter.mp hk).1
  have hkf : f k ≠ 0 := Finsupp.mem_support_iff.mp hkfmem
  simp [hvanish k hkf]

/-- In particular, convolution vanishes when the first input is zero. -/
@[simp] theorem convolutionCoeff_zero_of_first
    (g : FiniteFourier) (n : PeriodicFrequency) :
    convolutionCoeff (0 : FiniteFourier) g n = 0 := by
  apply convolutionCoeff_eq_zero_of_pairwise_vanish
  simp

end NSFormalization.Paper1.PeriodicFinitePicardSupport
