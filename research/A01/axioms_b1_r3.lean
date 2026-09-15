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

#print axioms restrictPath
#print axioms restrictPath_apply
#print axioms restrict_leray
#print axioms restrict_advection
#print axioms reducedAdvectionPath
#print axioms reducedResidualPath
#print axioms reducedResidualPath_eq
#print axioms cylinderVelocity_hasDerivWithinAt
#print axioms reducedResidualPath_contDiffOn
#print axioms cylinderPath_contDiffOn
#print axioms reducedResidualDerivativePath
#print axioms reducedResidualPath_hasDerivWithinAt
#print axioms reducedResidualDerivativeOrdinaryPath
#print axioms residualPath_hasDerivAt
#print axioms exists_contDiff_datumPath_of_cylinder
#print axioms datumPath_contDiffOn
#print axioms datumPath_contDiffOn_one
#print axioms datumPath_contDiffOn_all_orders

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Non-vacuity: R3 applies to the explicitly assigned zero cylinder and ordinary paths.
example :
    ∃ G : ℝ → RealVectorSobolev ((0 : ℕ) : ℝ),
      ContDiffOn ℝ 0 G (Icc (0 : ℝ) 1) ∧
      ∀ t : Icc (0 : ℝ) 1, IsSobolevDatum ((0 : ℕ) : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (G t.1) := by
  have hfs : ContDiffOn ℝ ∞
      (extendPath 1 (by norm_num) (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)))
      (Icc (0 : ℝ) 1) := by
    apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ =>
      (0 : SobolevSpace 1 6)) (Icc (0 : ℝ) 1)).congr
    intro t ht
    simp only [extendPath, ContinuousMap.zero_apply]
  have hduh : ∀ t : Icc (0 : ℝ) 1,
      (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)) t =
        quadraticDuhamel 1 (1 : ℝ) (by norm_num) (by norm_num) le_rfl
          (coefficients 1 (by norm_num : 6 ≤ 6)
            (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)))
          (0 : SobolevSpace 1 7)
          (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)) t := by
    intro t
    simp [quadraticDuhamel, source_eq]
  exact datumPath_contDiffOn (q := 6) (m := 0) (j := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (0 : SobolevSpace 1 7)
    (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6))
    (u := (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)))
    (U := (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)))
    hfs (fun t => by simp [value]) (fun θ t => by simp) hduh

end
