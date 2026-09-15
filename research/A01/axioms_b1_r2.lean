import NSFormalization.Section4.A01.DatumPathDeriv
import Euler.SmoothL2Series

noncomputable section

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerMeanOrdinaryLift EulerMeanSmoothRepresentative
open EulerCylinderSobolevSpace EulerLiftedGradientSpace EulerSmoothFieldSobolevTime
open EulerQuadraticSource EulerVolterraConvolution
open NSFormalization.Source.ForcedCylinderLocal
open NSFormalization.Section4.D01
open NSFormalization.Paper3 (RealVectorSobolev)
open NavierStokes.ProblemStatement (Space)

open NSFormalization.Section4.A01

#print axioms lowerDatumL_injective
#print axioms lowerVectorL_injective
#print axioms cylinderSourcePath
#print axioms cylinderResidualPath
#print axioms cylinderResidual
#print axioms cylinderResidual_value
#print axioms laplacianOperator_translation_local
#print axioms cylinderResidual_invariant
#print axioms ordinaryResidualPath
#print axioms ordinaryResidualPath_eq_ordinaryDerivative
#print axioms ordinaryLift_adjoint_of_invariant
#print axioms ordinaryLift_ordinaryResidualPath
#print axioms sobolevPath_angle_invariant
#print axioms projectedResidualPath
#print axioms projectedResidualOrdinaryPath
#print axioms projectedResidualPath_eq
#print axioms ordinaryLift_projectedResidualOrdinaryPath
#print axioms weakDerivsBound_cylinder
#print axioms datum_sub_norm_sq_le_general
#print axioms exists_continuous_datumPath_general
#print axioms datumPath_hasDerivAt
#print axioms exists_differentiable_datumPath
#print axioms residualDatum_is_timeDerivative

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

-- Non-vacuity: the R2 theorem applies to the zero solution and zero force.
-- The explicit assignments `u := 0` and `U := 0` occur in the theorem application below.
set_option maxHeartbeats 400000 in
example :
    ∃ A R : C(Icc (0 : ℝ) 1, RealVectorSobolev ((0 : ℕ) : ℝ)),
      (∀ t, IsSobolevDatum ((0 : ℕ) : ℝ)
        (⇑((0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2)) t)) (A t)) ∧
      ∀ (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1),
        HasDerivAt (extendPath 1 (by norm_num) A) (R ⟨t, ht.1.le, ht.2.le⟩) t := by
  let F : Icc (0 : ℝ) 1 → SmoothL2Field Space := fun _ => zeroField
  have hF : ∀ n, Continuous fun t => (F t).jetLp n := by
    intro n
    simpa only [F, EulerSmoothL2Series.zeroField_jet] using
      (continuous_const : Continuous (fun _ : Icc (0 : ℝ) 1 =>
        (0 : Lp (Space [×n]→L[ℝ] Space) 2 volume)))
  have ha0 : ordinarySobolev 7 (zeroField : SmoothL2Field Space).toLp
      (zeroField : SmoothL2Field Space).translation_contDiff = 0 := by
    apply value_injective 1
    calc
      value 1 (ordinarySobolev 7 (zeroField : SmoothL2Field Space).toLp
          (zeroField : SmoothL2Field Space).translation_contDiff) =
          ordinaryLift (zeroField : SmoothL2Field Space).toLp :=
        ordinarySobolev_value 7 _ _
      _ = ordinaryLift 0 := congrArg ordinaryLift EulerSmoothL2Series.zeroField_value
      _ = value 1 (0 : SobolevSpace 1 7) := rfl
  have hf0 : sobolevPath F hF 6 = 0 := by
    apply ContinuousMap.ext
    intro t
    apply value_injective 1
    calc
      value 1 (sobolevPath F hF 6 t) = ordinaryLift (F t).toLp :=
        ordinarySobolev_value 6 _ _
      _ = ordinaryLift 0 := congrArg ordinaryLift EulerSmoothL2Series.zeroField_value
      _ = value 1 ((0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 6)) t) := rfl
  have hduh : ∀ t : Icc (0 : ℝ) 1,
      (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)) t =
        quadraticDuhamel 1 (1 : ℝ) (by norm_num) (by norm_num) le_rfl
          (coefficients 1 (by norm_num : 6 ≤ 6) (sobolevPath F hF 6))
          (ordinarySobolev 7 (zeroField : SmoothL2Field Space).toLp
            (zeroField : SmoothL2Field Space).translation_contDiff)
          (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7)) t := by
    intro t
    rw [ha0, hf0]
    simp [quadraticDuhamel, source_eq]
  obtain ⟨A, R, hA, _, hderiv⟩ :=
    exists_differentiable_datumPath (by norm_num : 6 ≤ 6)
      (by norm_num : 0 ≤ 6 - 1) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) (zeroField : SmoothL2Field Space) F hF
      (0 : C(Icc (0 : ℝ) 1, SobolevSpace 1 7))
      (0 : C(Icc (0 : ℝ) 1, EulerMeanSolenoidal.L2))
      (fun θ t => by simp) (fun t => by simp [value]) hduh
  exact ⟨A, R, hA, hderiv⟩

end
