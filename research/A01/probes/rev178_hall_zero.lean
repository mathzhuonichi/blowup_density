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

-- Reviewer non-vacuity for the named all-order supply hypothesis.
example :
    ∀ j m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      ContDiffOn ℝ j G (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum (m : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (G t.1) := by
  apply datumPath_contDiffOn_all_orders (ν := 1) (S := 1)
    (by norm_num) (by norm_num)
    (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
  intro q hq
  refine ⟨0, 0, 0, ?_, ?_, ?_, ?_⟩
  · apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ =>
        (0 : SobolevSpace 1 q)) (Icc (0 : ℝ) 1)).congr
    intro t ht
    simp only [extendPath, ContinuousMap.zero_apply]
  · intro t
    simp [value]
  · intro θ t
    simp
  · intro t
    simp [quadraticDuhamel, source_eq]

end
