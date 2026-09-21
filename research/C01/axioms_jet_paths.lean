import NSFormalization.Section4.C01.JetPaths
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 146-C01-jet-paths
(`Section4/C01/JetPaths.lean`).  Every declaration must depend on exactly
`[propext, Classical.choice, Quot.sound]`.

Non-vacuity: the paths and their continuities are instantiated on the genuine
classical solution `A04.zeroSol` (`Section4/A04/ZeroSolution.lean`, PR #145) with
`A04.memForceR_zero`, so the theorems below are not vacuously typed.
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerSmoothLimit

namespace NSFormalization.Section4.C01

-- Force path.
#print axioms forcePath
#print axioms forcePath_field
#print axioms forcePath_jetLp_continuous

-- Advection path.
#print axioms advectionPath
#print axioms advectionPath_field
#print axioms advectionPath_jetLp_continuous

-- Laplacian jet-continuity tools and path.
#print axioms sumField_jetLp_continuous
#print axioms laplacianField_jetLp_continuous
#print axioms laplacianPath
#print axioms laplacianPath_field
#print axioms laplacianPath_jetLp_continuous

-- Viscous (ν-scaled Laplacian) path.
#print axioms viscousPath
#print axioms viscousPath_field
#print axioms viscousPath_jetLp_continuous

-- Momentum residual path.
#print axioms residualPath
#print axioms residualPath_field
#print axioms residualPath_jetLp_continuous
#print axioms temporalDerivative_eq_residual_sub_pressureGradient

-- Non-vacuity on the zero classical solution `A04.zeroSol : ClassicalSolutionR 1 0 0 2`.
example : Continuous (fun t : Icc (0 : ℝ) 1 =>
    (residualPath (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
      (by norm_num) t).jetLp 0) :=
  residualPath_jetLp_continuous _ _ _ 0

example (x : Space) :
    let w := A04.zeroSol 1 2 (by norm_num) (by norm_num)
    let t : Icc (0 : ℝ) 1 := ⟨1, Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩⟩
    NavierStokes.ProblemStatement.temporalDerivative w.velocity 1 x
      = (residualPath w A04.memForceR_zero (by norm_num) t).field x
          - NavierStokes.ProblemStatement.pressureGradient w.pressure 1 x :=
  temporalDerivative_eq_residual_sub_pressureGradient
    (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero (by norm_num)
    (⟨1, Set.mem_Icc.mpr ⟨by norm_num, le_refl 1⟩⟩ : Icc (0 : ℝ) 1) (by norm_num) x

end NSFormalization.Section4.C01
