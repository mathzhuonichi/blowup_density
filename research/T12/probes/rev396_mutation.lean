import NSFormalization.Section3.T12.CriticalL3

noncomputable section

namespace NSFormalization.Section3.T12

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Section3.T10
open NSFormalization.Section3.T13
open NSFormalization.Section4.A02 (SpatialField)
open NSFormalization.Section4.A05 (criticalL3Const criticalL3Const_pos)
open NSFormalization.Section4.D01 (dotHomogeneousENorm)
open scoped ContDiff ENNReal BigOperators

theorem rev396_zero_constant (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmean : IsMeanZeroT v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal (0 : ℝ) * periodicHomogeneousENorm (1 / 2) v := by
  by_cases hfin : periodicHomogeneousENorm (1 / 2) v = ⊤
  · rw [hfin, ENNReal.mul_top (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact CcriticalHalf_pos)]
    exact le_top
  · have hmem : MemPeriodicHomogeneous (1 / 2) v :=
      ⟨hv.2, memLp_torusLift_vector hv.1.continuous 2, hmean, hfin⟩
    have hL := l2Q_le_homogeneous_half v hv hmem
    have halg : ENNReal.ofReal criticalL3Const *
          (ENNReal.ofReal cutoffGagliardoConst *
            (ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v
              + periodicHomogeneousENorm (1 / 2) v))
        = ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v := by
      have hg : ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v
            + periodicHomogeneousENorm (1 / 2) v
          = ENNReal.ofReal (gapConst (1 / 2) + 1) * periodicHomogeneousENorm (1 / 2) v := by
        rw [ENNReal.ofReal_add (gapConst_pos (1 / 2) (by norm_num)).le zero_le_one,
          ENNReal.ofReal_one, add_mul, one_mul]
      have hc : ENNReal.ofReal CcriticalHalf
          = ENNReal.ofReal criticalL3Const * ENNReal.ofReal cutoffGagliardoConst
              * ENNReal.ofReal (gapConst (1 / 2) + 1) := by
        unfold CcriticalHalf
        rw [ENNReal.ofReal_mul (mul_nonneg criticalL3Const_pos.le cutoffGagliardoConst_pos.le),
          ENNReal.ofReal_mul criticalL3Const_pos.le]
      rw [hg, hc]; ring
    calc periodicLpENorm 3 v
        = eLpNorm v 3 (volume.restrict fundamentalCube) :=
          periodicLpENorm_eq_restrict v hv.2 3
      _ = eLpNorm (cutoffMul v) 3 (volume.restrict fundamentalCube) :=
          eLpNorm_congr_ae (ae_restrict_of_forall_mem measurableSet_fundamentalCube
            (fun x hx => (cutoffMul_eq_on_cube v hx).symm))
      _ ≤ eLpNorm (cutoffMul v) 3 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
      _ ≤ ENNReal.ofReal criticalL3Const * dotHomogeneousENorm (1 / 2) (cutoffMul v) := by
          have h := NSFormalization.Section4.A05.velocityCriticalL3 (cutoffMul v)
            (memHInfty_cutoffMul hv.1)
          rw [a05_dotHomogeneousENorm_eq] at h
          exact h
      _ ≤ ENNReal.ofReal criticalL3Const *
            (ENNReal.ofReal cutoffGagliardoConst *
              (eLpNorm v 2 (volume.restrict fundamentalCube)
                + periodicHomogeneousENorm (1 / 2) v)) := by
          gcongr
          exact cutoff_gagliardo_half v hv hmean
      _ ≤ ENNReal.ofReal criticalL3Const *
            (ENNReal.ofReal cutoffGagliardoConst *
              (ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v
                + periodicHomogeneousENorm (1 / 2) v)) := by
          gcongr
      _ = ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v := halg

end NSFormalization.Section3.T12
