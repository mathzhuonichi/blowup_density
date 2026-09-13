import NSFormalization.Paper1.PeriodicFinitePicardSupport

noncomputable section
namespace NSFormalization.Paper1.PeriodicFinitePicardSupportClosure

open NSFormalization.Paper1.PeriodicPicardBilinear
open NSFormalization.Paper1.PeriodicFinitePicardSupport
open scoped BigOperators

abbrev FiniteFourier := PeriodicPicardBilinear.FiniteFourier

theorem convolutionCoeff_eq_zero_of_not_mem_add
    (f g : FiniteFourier) (S T : Finset PeriodicFrequency)
    (hf : f.support ⊆ S) (hg : g.support ⊆ T)
    {n : PeriodicFrequency} (hn : n ∉ (S.product T).image (fun p => p.1 + p.2)) :
    convolutionCoeff f g n = 0 := by
  apply convolutionCoeff_eq_zero_of_pairwise_vanish
  intro k hk
  by_contra hgn
  have hfk : k ∈ f.support := Finsupp.mem_support_iff.mpr hk
  have hkt : k ∈ S := hf hfk
  have hgt : n - k ∈ g.support := Finsupp.mem_support_iff.mpr hgn
  have hnt : n - k ∈ T := hg hgt
  apply hn
  exact by
    simp only [Finset.mem_image]
    exact ⟨(k, n - k), Finset.mem_product.mpr ⟨hkt, hnt⟩, by ring⟩

end NSFormalization.Paper1.PeriodicFinitePicardSupportClosure
