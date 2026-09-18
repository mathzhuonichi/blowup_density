import NSFormalization.Section3.T12.CutoffGagliardo
import NSFormalization.Section3.T12.HaarCube
import NSFormalization.Section3.T12.SpectralGap
import NSFormalization.Section3.T15.ParsevalZero
import NSFormalization.Section4.A05.CriticalL3

/-!
# T12 U4: the mean-zero torus critical embedding `velocityCriticalL3`

For a smooth mean-zero periodic vector field `v`, the physical `L³(T³)` norm is
controlled by the homogeneous `Ḣ^{1/2}(T³)` norm
(`appendix-b-embeddings.tex:20-31`, `03-torus.tex`; `research/T12/T12_SPLIT.md` U4).

## Route (reverse localization, `research/T12/T12_SPLIT.md` U4)

`periodicLpENorm 3 v = eLpNorm v 3 (volume.restrict fundamentalCube)`
(`HaarCube.periodicLpENorm_eq_restrict`)
`= eLpNorm (cutoffMul v) 3 (volume.restrict fundamentalCube)` (`cutoffMul v = v` on
`fundamentalCube`, `Cutoff.cutoffMul_eq_on_cube`) `≤ eLpNorm (cutoffMul v) 3 volume`
(`Measure.restrict_le_self`); the **registered** whole-space embedding
`Section4.A05.velocityCriticalL3` applied to the smooth compactly supported
`cutoffMul v` (its `MemHInfty` from `Cutoff.memHInfty_cutoffMul`), with the norm
spelling bridged by `A05.dotHomogeneousENorm = D01.dotHomogeneousENorm` (rfl,
`a05_dotHomogeneousENorm_eq`), gives `≤ criticalL3Const · dotHomogeneousENorm (1/2)
(cutoffMul v)`; the U3 core `cutoff_gagliardo_half` bounds that by
`cutoffGagliardoConst · (‖v‖_{L²(Q)} + periodicHomogeneousENorm (1/2) v)`; and the
spectral gap absorbs the physical `L²(Q)` remainder into the homogeneous norm
(`l2Q_le_homogeneous_half`, via `ParsevalZero` + a Sobolev order-monotonicity step
`periodicSobolevENorm_zero_le_half` + `SpectralGap.spectralGap`).

## Smoothness note

The API field `velocityCriticalL3` quantifies over `MemPeriodicHomogeneous (1/2) v`,
which does **not** carry smoothness, while both analytic inputs
(`cutoff_gagliardo_half` and `A05.velocityCriticalL3` through `memHInfty_cutoffMul`)
require a smooth field.  This module proves the smooth-mean-zero form
`velocityCriticalL3_smooth`; passing from a general `MemPeriodicHomogeneous (1/2)`
datum to the smooth core is a torus density/mollification argument recorded as the
residual in `research/T12/ATTEMPTS_U4.md`.
-/

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

/-! ## §1  The homogeneous-norm spelling bridge -/

/-- Lane 165's local homogeneous norm and D01's registered implementation norm
are the same datum-infimum body (`Bindings/GradientL6V2.lean:44`,
"canonical norm: rfl").  Used explicitly at the A05 application below rather than
assuming defeq silently. -/
theorem a05_dotHomogeneousENorm_eq :
    NSFormalization.Section4.A05.dotHomogeneousENorm = dotHomogeneousENorm := rfl

/-! ## §2  Sobolev order-zero ≤ order-half (physical `L²` ≤ inhomogeneous `H^{1/2}`) -/

/-- The inhomogeneous total periodic Sobolev extended norm is monotone in the
order: at order `0` it is dominated by the order-`1/2` norm.  Proof: from any
order-`1/2` datum of `v`, the bounded even multiplier
`periodicFrequencyWeight k ^ ((0 - 1/2)/2)` (absolute value `≤ 1` since the weight
is `≥ 1` and the exponent is nonpositive) produces the order-`0` datum with no
larger `ℓ²` norm. -/
theorem periodicSobolevENorm_zero_le_half (v : SpatialField) :
    periodicSobolevENorm 0 v ≤ periodicSobolevENorm (1 / 2) v := by
  unfold periodicSobolevENorm
  refine le_iInf (fun A => ?_)
  set w : PeriodicFrequency → ℝ :=
    fun k => periodicFrequencyWeight k ^ (((0 : ℝ) - 1 / 2) / 2) with hw
  have hbound : ∀ k, |w k| ≤ 1 := by
    intro k
    simp only [hw]
    rw [abs_of_pos (Real.rpow_pos_of_pos
      (lt_of_lt_of_le zero_lt_one (one_le_fourierWeight k)) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_fourierWeight k) (by norm_num)
  have heven : ∀ k, w (-k) = w k := by
    intro k; simp only [hw]; rw [fourierWeight_neg]
  have hmem0 : reweightDatum w 1 zero_le_one hbound A.1.1 ∈ realPeriodicSubmodule :=
    reweightDatum_real w 1 zero_le_one hbound heven A.1
  have hdatum : IsPeriodicDatum 0 v ⟨reweightDatum w 1 zero_le_one hbound A.1.1, hmem0⟩ := by
    refine ⟨A.2.1, A.2.2.1, ?_⟩
    intro i k
    have hscal : w k * periodicFrequencyWeight k ^ (((1 : ℝ) / 2) / 2)
        = periodicFrequencyWeight k ^ ((0 : ℝ) / 2) := by
      simp only [hw]
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one (one_le_fourierWeight k))]
      congr 1; norm_num
    show reweightDatum w 1 zero_le_one hbound A.1.1 i k
        = periodicFrequencyWeight k ^ ((0 : ℝ) / 2)
          • periodicFourierCoeff (fun x => ((v x i : ℝ) : ℂ)) k
    rw [reweightDatum_apply, A.2.2.2 i k]
    simp only [smul_eq_mul, Complex.real_smul]
    rw [← mul_assoc, ← Complex.ofReal_mul, hscal]
  refine le_trans
    (iInf_le_of_le ⟨⟨reweightDatum w 1 zero_le_one hbound A.1.1, hmem0⟩, hdatum⟩ le_rfl) ?_
  have hnorm : ‖reweightDatum w 1 zero_le_one hbound A.1.1‖ₑ ≤ ‖A.1.1‖ₑ := by
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal
      (by simpa only [one_mul] using reweightDatum_norm_le w 1 zero_le_one hbound A.1.1)
  exact hnorm

/-! ## §3  The physical `L²(Q)` remainder is absorbed by the homogeneous norm -/

/-- The physical `L²(fundamentalCube)` norm of a smooth mean-zero homogeneous field
is bounded by `gapConst (1/2)` times its homogeneous `Ḣ^{1/2}(T³)` norm.  Route:
Haar↔cube transfer (`HaarCube`), order-zero Parseval (`ParsevalZero`),
Sobolev order monotonicity (`periodicSobolevENorm_zero_le_half`), and the spectral
gap (`SpectralGap.spectralGap`). -/
theorem l2Q_le_homogeneous_half (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmem : MemPeriodicHomogeneous (1 / 2) v) :
    eLpNorm v 2 (volume.restrict fundamentalCube)
      ≤ ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v := by
  calc eLpNorm v 2 (volume.restrict fundamentalCube)
      = eLpNorm (torusLift v) 2 periodicTorusMeasure :=
        (eLpNorm_torusLift_eq_restrict v hv.2 2).symm
    _ = periodicSobolevENorm 0 v :=
        (NSFormalization.Section3.T15.periodicSobolevENorm_zero_eq v hv).symm
    _ ≤ periodicSobolevENorm (1 / 2) v := periodicSobolevENorm_zero_le_half v
    _ ≤ ENNReal.ofReal (gapConst (1 / 2)) * periodicHomogeneousENorm (1 / 2) v :=
        spectralGap (1 / 2) (by norm_num) v hmem

/-! ## §4  The explicit constant -/

/-- The explicit U4 constant: the whole-space critical constant, the U3
reverse-localization constant, and the `1 + gapConst (1/2)` absorption factor. -/
def CcriticalHalf : ℝ :=
  criticalL3Const * cutoffGagliardoConst * (gapConst (1 / 2) + 1)

/-- `0 < CcriticalHalf`. -/
theorem CcriticalHalf_pos : 0 < CcriticalHalf := by
  have h3 : 0 < gapConst (1 / 2) + 1 := by
    have := gapConst_pos (1 / 2) (by norm_num); linarith
  exact mul_pos (mul_pos criticalL3Const_pos cutoffGagliardoConst_pos) h3

/-! ## §5  The U4 target (smooth mean-zero form) -/

/-- **T12 U4 (smooth mean-zero form), `appendix-b-embeddings.tex:20-31`.**
For a smooth mean-zero periodic vector field `v`, the physical `L³(T³)` norm is
bounded by the homogeneous `Ḣ^{1/2}(T³)` norm with the explicit positive constant
`CcriticalHalf`.  This is the API field `velocityCriticalL3` under the smoothness
that its two analytic inputs require; the general `MemPeriodicHomogeneous (1/2)`
case is the density residual of `research/T12/ATTEMPTS_U4.md`. -/
theorem velocityCriticalL3_smooth (v : SpatialField) (hv : SmoothPeriodicT v)
    (hmean : IsMeanZeroT v) :
    periodicLpENorm 3 v ≤ ENNReal.ofReal CcriticalHalf * periodicHomogeneousENorm (1 / 2) v := by
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
