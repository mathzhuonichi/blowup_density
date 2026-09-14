-- Reviewer probe (lane 142 review, REVIEW_A3_M2.md), preserved verbatim; compiles on this branch.
/- Lane 142 review probe 5: (i) the `(2:ℝ)` vs `((2:ℕ):ℝ)` order literal is `rfl`;
   (ii) the manuscript case `T₀ := T` (uniform up to S) is an instance;
   (iii) on a `ClassicalSolutionR` the order-2 norm is a genuine datum norm (no ⊤-trap). -/
import NSFormalization.Section4.A01.GronwallInstance

open Set MeasureTheory
open NSFormalization.Section4.A04
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR IsSobolevDatum)

noncomputable section
namespace Rev142P5

example (u : SpaceTimeField) (t : ℝ) :
    sobolevNormAt (((2 : ℕ) : ℝ)) u t = sobolevNormAt (2 : ℝ) u t := rfl

/-- (ii) The manuscript sentence `appendix-a-local-theory.tex:146-147` is the `T₀ := T` case:
`hkbnd` is then eq:criterion on all of `[0,T)` and the conclusion is "uniformly up to `S`". -/
theorem manuscript_case_T₀_eq_T
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (hν : 0 < ν) (ha : a ∈ initialClassR) (hf : MemForceR f) (hf1 : MemL1Hm f)
    (w : ClassicalSolutionR ν a f T) (hpath : HasSmoothSobolevPath T w.velocity)
    {m : ℕ} (hm : 3 ≤ m) {Kbnd : ℝ} (hT : 0 < T)
    (hcrit : ∀ t ∈ Ico (0 : ℝ) T,
        (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd) :
    ∀ t ∈ Ico (0 : ℝ) T,
      sobolevNormAt (m : ℝ) w.velocity t ≤
        (sobolevNormAt (m : ℝ) w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal)
          * Real.exp (Cgron m ν * Kbnd) :=
  NSFormalization.Section4.A01.highOrder_bddAbove_of_kbnd hν ha hf hf1 w hpath hm hT le_rfl hcrit

/-- (iii) No `⊤`-trap on the R³ classical-solution side: `w.sobolev 2` hands over a genuine
order-2 datum at every `t ∈ [0,T)`, so `sobolevNormAt 2 w.velocity t` is a real Sobolev norm
(`= ‖G t‖`), not the junk value `0` that `sobolevENorm = ⊤` would produce. -/
theorem order2_norm_is_genuine
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) :
    ∃ G : ℝ → NSFormalization.Paper3.RealVectorSobolev ((2 : ℕ) : ℝ),
      ∀ t ∈ Ico (0 : ℝ) T, sobolevNormAt 2 w.velocity t = ‖G t‖ := by
  obtain ⟨G, _hGc, hGd⟩ := w.sobolev 2
  exact ⟨G, fun t ht => sobolevNormAt_eq (hGd t ht)⟩

end Rev142P5
