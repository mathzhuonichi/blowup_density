import NSFormalization.Section4.A01.DatumPathSmooth

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerMeanOrdinaryLift EulerCylinderSobolevSpace
open EulerVolterraConvolution EulerQuadraticSource
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Section4.A01
open scoped ContDiff

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Reviewer non-vacuity: the main theorem genuinely reaches a positive R3 rung (j = 2).
example :
    ∃ G : ℝ → RealVectorSobolev ((0 : ℕ) : ℝ),
      ContDiffOn ℝ 2 G (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum ((0 : ℕ) : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (G t.1) := by
  have hfs : ContDiffOn ℝ ∞
      (extendPath 1 (by norm_num) (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 9)))
      (Icc (0 : ℝ) 1) := by
    apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ =>
      (0 : SobolevSpace 1 9)) (Icc (0 : ℝ) 1)).congr
    intro t ht
    simp only [extendPath, ContinuousMap.zero_apply]
  have hduh : ∀ t : Icc (0 : ℝ) 1,
      (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 10)) t =
        quadraticDuhamel 1 (1 : ℝ) (by norm_num) (by norm_num) le_rfl
          (coefficients 1 (by norm_num : 6 ≤ 9)
            (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 9)))
          (0 : SobolevSpace 1 10)
          (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 10)) t := by
    intro t
    simp [quadraticDuhamel, source_eq]
  exact datumPath_contDiffOn (q := 9) (m := 0) (j := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (0 : SobolevSpace 1 10)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 9))
    (u := (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 10)))
    (U := (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)))
    hfs (fun t => by simp [value]) (fun θ t => by simp) hduh

end
