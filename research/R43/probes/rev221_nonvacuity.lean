import NSFormalization.Section4.R43.ForcePath
open Set MeasureTheory
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField)
open NSFormalization.Section4.R43

-- A positive-length interval, with all bootstrap hypotheses instantiated.
example : ∀ t ∈ Icc (0 : ℝ) 1,
    criticalNormAt (NSFormalization.Section4.A04.zeroSol 1 2
      (by norm_num) (by norm_num)).velocity t ≤ 0 * 1 := by
  apply critical_bootstrap_zero_datum (by norm_num)
    NSFormalization.Section4.A04.memForceR_zero
    (NSFormalization.Section4.A04.zeroSol 1 2 (by norm_num) (by norm_num))
    (by norm_num) (by norm_num) (by norm_num)
    (one_div_pos.mpr (mul_pos (by norm_num) trilinearConst_pos))
  have hz : ∀ s : ℝ, criticalForceAt (0 : SpaceTimeField) s = 0 := by
    intro s
    change (NSFormalization.Section4.D01.dotHomogeneousENorm (1 / 2)
      (0 : SpatialField)).toReal = 0
    rw [NSFormalization.Section4.D01.dotHomogeneousENorm_zero]
    rfl
  simp [criticalForcePrimitive, hz]
