import NSFormalization.Section4.C01.PressureJetPath
import NSFormalization.Section4.A04.ZeroSolution

/-!
Transitive-axiom audit for lane 148-C01-e4b-pressure-jets
(`Section4/C01/PressureJetPath.lean`).  Every declaration must depend on exactly
`[propext, Classical.choice, Quot.sound]`.

Non-vacuity: the pressure-gradient / derivative jet-continuities are instantiated on the
genuine classical solution `A04.zeroSol` (`Section4/A04/ZeroSolution.lean`) with
`A04.memForceR_zero` over the **non-degenerate** interior window `[1/2,1] ⊂ (0,2)` (at jet
orders `0` and `2`), so continuity is not trivial for type-theoretic reasons.
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field

namespace NSFormalization.Section4.C01

-- Glue (a): jet control of the finite-order weak-derivative bound.
#print axioms norm_jetPostcompose_le
#print axioms norm_jetLp_mapField_le
#print axioms norm_directionalField_jetLp_le
#print axioms hasWeakDerivsL2Bound_of_jetLp_sq_le

-- Item 2: jets ⟹ datum-path continuity.
#print axioms norm_smoothAngularDatum_sub_sq_le
#print axioms smoothAngularDatum_path_continuous

-- Item 3 + supporting: the interior-window residual path and the pressure-gradient jets.
#print axioms residualPathIcc
#print axioms residualPathIcc_field
#print axioms residualPathIcc_jetLp_continuous
#print axioms mem_Ioo_of_mem_Icc
#print axioms pressureGradientPath_jetLp_continuous

-- Item 4: the derivative slice (the `hB` clause of E4).
#print axioms temporalSlicePath_jetLp_continuous

-- Non-vacuity on the zero classical solution `A04.zeroSol : ClassicalSolutionR 1 0 0 2`,
-- over the non-degenerate window `[1/2,1] ⊂ (0,2)`, at jet orders 0 and 2.
example : Continuous (fun t : Icc (1 / 2 : ℝ) 1 =>
    (pressureGradientField (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
      (mem_Ioo_of_mem_Icc (by norm_num) (by norm_num) t.2)).jetLp 0) :=
  pressureGradientPath_jetLp_continuous (A04.zeroSol 1 2 (by norm_num) (by norm_num))
    A04.memForceR_zero (by norm_num) (by norm_num) 0

example : Continuous (fun t : Icc (1 / 2 : ℝ) 1 =>
    (temporalSliceField (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
      (mem_Ioo_of_mem_Icc (by norm_num) (by norm_num) t.2)).jetLp 2) :=
  temporalSlicePath_jetLp_continuous (A04.zeroSol 1 2 (by norm_num) (by norm_num))
    A04.memForceR_zero (by norm_num) (by norm_num) 2

end NSFormalization.Section4.C01
