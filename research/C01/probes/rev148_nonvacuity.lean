import NSFormalization.Section4.C01.PressureJetPath
import NSFormalization.Section4.A04.ZeroSolution

/-!
Reviewer probe 3 for lane 148: the axioms file instantiates the window as `Icc (1:ℝ) 1`,
a one-point index type, on which `Continuous` is trivial for type reasons.  A genuinely
non-degenerate window `[1/2, 1] ⊂ (0,2)` also elaborates — offered as the one-line
strengthening of `research/C01/axioms_e4b.lean`.  (EXPECTED TO SUCCEED.)
-/

open Set MeasureTheory
open EulerLpTranslation EulerLpTranslation.SmoothL2Field

namespace NSFormalization.Section4.C01

example : Continuous (fun t : Icc (1/2 : ℝ) 1 =>
    (pressureGradientField (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
      (mem_Ioo_of_mem_Icc (by norm_num) (by norm_num) t.2)).jetLp 0) :=
  pressureGradientPath_jetLp_continuous (A04.zeroSol 1 2 (by norm_num) (by norm_num))
    A04.memForceR_zero (by norm_num) (by norm_num) (by norm_num) 0

example : Continuous (fun t : Icc (1/2 : ℝ) 1 =>
    (temporalSliceField (A04.zeroSol 1 2 (by norm_num) (by norm_num)) A04.memForceR_zero
      (mem_Ioo_of_mem_Icc (by norm_num) (by norm_num) t.2)).jetLp 2) :=
  temporalSlicePath_jetLp_continuous (A04.zeroSol 1 2 (by norm_num) (by norm_num))
    A04.memForceR_zero (by norm_num) (by norm_num) (by norm_num) 2

end NSFormalization.Section4.C01
