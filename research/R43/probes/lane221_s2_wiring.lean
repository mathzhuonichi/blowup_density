import NSFormalization.Section4.R43.ForcePath

open Set MeasureTheory
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR MemForceR)
open NSFormalization.Section4.R43

/-! The promoted proof applies `criticalNormBound_radius` to the energy
inequality from `rcritical1_of_classical'` and the actual force primitive.
The compact endpoint S must lie strictly inside the classical lifespan T. -/
example {ν T S c : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν (0 : SpatialField) f T)
    (hS : 0 ≤ S) (hST : S < T)
    (hc0 : 0 ≤ c) (hclt : c < 1 / (2 * trilinearConst))
    (hsmall : (∫ s in (0 : ℝ)..S, criticalForceAt f s) ≤ c * ν) :
    ∀ t ∈ Icc (0 : ℝ) S, criticalNormAt w.velocity t ≤ c * ν := by
  exact critical_bootstrap_zero_datum hν hf w hS hST hc0 hclt hsmall

/-! The inhomogeneous S6 smallness condition supplies the same input. -/
example {ν T S c : ℝ} {f : SpaceTimeField}
    (hν : 0 < ν) (hf : MemForceR f)
    (w : ClassicalSolutionR ν (0 : SpatialField) f T)
    (hS : 0 ≤ S) (hST : S < T)
    (hc0 : 0 ≤ c) (hclt : c < 1 / (2 * trilinearConst))
    (hsmall : (NSFormalization.Section4.D01.forceSobolevENormL1 (1 / 2) f).toReal
      ≤ c * ν) :
    ∀ t ∈ Icc (0 : ℝ) S, criticalNormAt w.velocity t ≤ c * ν := by
  exact critical_bootstrap_zero_datum hν hf w hS hST hc0 hclt
    ((criticalForcePrimitive_le_forceSobolevENormL1 hf hS).trans hsmall)

/-! An actual classical solution, including the degenerate compact interval. -/
example : ∀ t ∈ Icc (0 : ℝ) 0,
    criticalNormAt (NSFormalization.Section4.A04.zeroSol 1 1
      (by norm_num) (by norm_num)).velocity t ≤ 0 * 1 := by
  exact critical_bootstrap_zero_datum (by norm_num)
    NSFormalization.Section4.A04.memForceR_zero
    (NSFormalization.Section4.A04.zeroSol 1 1 (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num)
    (one_div_pos.mpr (mul_pos (by norm_num) trilinearConst_pos))
    (by simp)
