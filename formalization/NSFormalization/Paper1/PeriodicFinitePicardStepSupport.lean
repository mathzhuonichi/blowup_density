import NSFormalization.Paper1.PeriodicFinitePicardCoeff
import NSFormalization.Paper1.PeriodicFinitePicardSupportClosure

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardStepSupport

open Set MeasureTheory
open NSFormalization.Paper1.PeriodicHeatMultiplier
open NSFormalization.Paper1.PeriodicPicardBilinear
open NSFormalization.Paper1.PeriodicFinitePicardCoeff
open NSFormalization.Paper1.PeriodicFinitePicardSupportClosure

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

theorem picardCoeff_eq_zero_of_not_mem_support_union
    (ν : ℝ) (hν : 0 ≤ ν) (t : ℝ) (n : PeriodicFrequency)
    (u₀ : FiniteFourier) (u f : ℝ → FiniteFourier)
    (S₀ S R : Finset PeriodicFrequency)
    (h₀ : u₀.support ⊆ S₀)
    (hu : ∀ τ, (u τ).support ⊆ S)
    (hf : ∀ τ, (f τ).support ⊆ R)
    (hn : n ∉ S₀ ∪ (S.product S).image (fun p => p.1 + p.2) ∪ R) :
    picardCoeff ν hν t n u₀ u f = 0 := by
  unfold picardCoeff
  have hinit : u₀ n = 0 := by
    by_contra hzero
    have hnmem : n ∈ u₀.support := Finsupp.mem_support_iff.mpr hzero
    exact hn (Finset.mem_union_left _ (Finset.mem_union_left _ (h₀ hnmem)))
  have hforce : ∀ τ, convolutionCoeff (u τ) (u τ) n + f τ n = 0 := by
    intro τ
    have hconv : convolutionCoeff (u τ) (u τ) n = 0 :=
      convolutionCoeff_eq_zero_of_not_mem_add (u τ) (u τ) S S (hu τ) (hu τ)
        (by intro hm; exact hn (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
    have hfzero : f τ n = 0 := by
      by_contra hzero
      have hm : n ∈ (f τ).support := Finsupp.mem_support_iff.mpr hzero
      exact hn (Finset.mem_union_right _ (hf τ hm))
    simp [hconv, hfzero]
  simp [hinit, hforce]

end NSFormalization.Paper1.PeriodicFinitePicardStepSupport
