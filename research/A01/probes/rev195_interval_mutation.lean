import NSFormalization.Section4.A01.InteriorMomentum

noncomputable section

namespace NSFormalization.Section4.A01

open Set Filter MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01

-- Negative mutation: widen the ambient-derivative conclusion from `Ioo` to
-- `Icc`.  The original proof must fail because an endpoint has no two-sided
-- neighborhood contained in the closed interval.
example {S s : ℝ} (hs : 2 ≤ s)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1))
    (G : ℝ → RealVectorSobolev s)
    (hG : ∀ t : Icc (0 : ℝ) S, IsSobolevDatum s (⇑(U t)) (G t.1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) S) (D : RealVectorSobolev s)
    (hderiv : HasDerivWithinAt G D (Icc (0 : ℝ) S) t) (x : Space) :
    temporalDerivative (jointRepresentative U hpaths) t x =
      vectorRepresentative s hs D x := by
  have hI : Icc (0 : ℝ) S ∈ nhds t := Icc_mem_nhds ht.1 ht.2
  have hd := vectorRepresentative_hasDerivAt hs (hderiv.hasDerivAt hI) x
  have heq : Filter.EventuallyEq (nhds t)
      (fun r => jointRepresentative U hpaths (r, x))
      (fun r => vectorRepresentative s hs (G r) x) := by
    filter_upwards [hI] with r hr
    exact congrFun (vectorRepresentative_eq_of_datums (by norm_num) hs
      (U ⟨r, hr⟩) ((Classical.choose_spec (hpaths 0 2)).2 ⟨r, hr⟩)
      (hG ⟨r, hr⟩)) x
  exact (hd.congr_of_eventuallyEq heq).deriv

end NSFormalization.Section4.A01
