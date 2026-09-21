import NSFormalization.Section4.A01.JointRepresentative

noncomputable section

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open scoped ContDiff

/- Negative mutation: widening the closed time interval to start at `-1` must
fail because `hpaths` controls the datum paths only on `[0,S]`. -/
example {S : ℝ} (hS : 0 < S)
    (U : C(Icc (0 : ℝ) S, EulerMeanSolenoidal.L2))
    (hpaths : ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) S) ∧
      ∀ t : Icc (0 : ℝ) S, IsSobolevDatum (m : ℝ) (⇑(U t)) (G t.1)) :
    ContDiffOn ℝ ∞ (jointRepresentative U hpaths)
      (Icc (-1 : ℝ) S ×ˢ (univ : Set Space)) := by
  exact jointRepresentative_contDiffOn hS U hpaths

end
