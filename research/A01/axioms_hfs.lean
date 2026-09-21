import NSFormalization.Section4.A01.ForcePathSmooth
import NSFormalization.Section4.A04.ZeroSolution

open Set NavierStokes.ProblemStatement
open EulerLpTranslation EulerLpTranslation.SmoothL2Field
open EulerSmoothFieldSobolevTime EulerVolterraConvolution
open scoped ContDiff

open NSFormalization.Section4
open NSFormalization.Section4.A01

#print axioms jetOfDatumCLM
#print axioms jetOfDatumCLM_apply
#print axioms datumWordCLM
#print axioms datumArrayCLM
#print axioms datumArrayCLM_eq_ordinarySobolev
#print axioms schwartzDatum
#print axioms denseRange_schwartzDatum
#print axioms schwartzRealField
#print axioms schwartzRealField_smooth
#print axioms schwartzSmoothField
#print axioms schwartzSmoothField_field
#print axioms schwartzDatum_isSobolevDatum
#print axioms datumArrayCLM_mem_sobolevSubspace
#print axioms datumSobolevCLM
#print axioms datumSobolevCLM_eq_ordinarySobolev
#print axioms forcePath_sobolevPath_contDiffOn
#print axioms forcePath_of_memForceR_smooth

/-- The main result has genuine content on an inhabited horizon for the zero force. -/
example :
    ContDiffOn ℝ ∞
      (extendPath 1 (by norm_num)
        (sobolevPath
          (NSFormalization.Section4.C01.forcePath
            (S := 1) (f := (0 : A02.SpaceTimeField)) A04.memForceR_zero)
          (NSFormalization.Section4.C01.forcePath_jetLp_continuous
            (S := 1) (f := (0 : A02.SpaceTimeField)) A04.memForceR_zero)
          6))
      (Icc (0 : ℝ) 1) :=
  forcePath_sobolevPath_contDiffOn
    (S := 1) (f := (0 : A02.SpaceTimeField)) A04.memForceR_zero (by norm_num) 6

/-- The extended lane-167 package is likewise inhabited by the canonical zero-force path. -/
example :
    ∃ F : Icc (0 : ℝ) 1 → SmoothL2Field Space,
      F = NSFormalization.Section4.C01.forcePath A04.memForceR_zero ∧
      (∀ n, Continuous fun t => (F t).jetLp n) ∧
      A04.MemL1Hm (0 : A02.SpaceTimeField) ∧
      ∀ q (_hq : 6 ≤ q),
        ∀ hF : ∀ n, Continuous fun t => (F t).jetLp n,
        ContDiffOn ℝ ∞
          (extendPath 1 (by norm_num)
            (sobolevPath F hF q))
          (Icc (0 : ℝ) 1) :=
  forcePath_of_memForceR_smooth A04.memForceR_zero (by norm_num)
