import NSFormalization.Section4.A01.ConstructorAssembly

/-! Reviewer probe: lane 178's all-`j,m` output feeds the assembly hypothesis
directly at `j = 0`; no continuity or datum adapter is needed. -/

noncomputable section

namespace Rev180HsobCompat

open Set
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

example {S : ℝ}
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (h178 : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1) := by
  intro m
  exact h178 0 m

end Rev180HsobCompat
