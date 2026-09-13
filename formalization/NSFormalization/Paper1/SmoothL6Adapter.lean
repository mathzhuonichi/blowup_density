import NavierStokes.R3.SmoothSobolevL6
import NavierStokes.R3.WeightedInterpolation

/-!
# Paper 1 adapters for the proved whole-space Sobolev and interpolation bounds

The source theorem `smooth_eLpNorm_six_toReal_le` is a genuine homogeneous
`H¹ → L⁶` estimate on `ℝ³` for a smooth field with finite `L²` value and
derivative norms.  This file packages that result for a fixed-time Paper 1
velocity slice.  The second theorem records the ordinary `L²`--`L⁶`
interpolation consequence.  It is deliberately not stated as, or used to
claim, the missing critical `H^(1/2) → L³` embedding.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace NSFormalization.Paper1

open NavierStokes.ProblemStatement
open NavierStokesR3.Comparison

abbrev velocitySlice (u : VelocityField) (t : ℝ) : Space → Space :=
  fun x => u (t, x)

/-- Whole-space `H¹ → L⁶` for a fixed-time Paper 1 velocity slice.

The hypotheses are exactly the source theorem's smoothness and finite endpoint
norm assumptions.  No periodicity, compact support, or fractional regularity
is inferred here.
-/
theorem velocitySlice_smooth_eLpNorm_six_toReal_le
    {u : VelocityField} {t : ℝ}
    (hsmooth : ContDiff ℝ 1 (velocitySlice u t))
    (h2 : MemLp (velocitySlice u t) 2 volume)
    (hD2 : MemLp (fderiv ℝ (velocitySlice u t)) 2 volume) :
    (eLpNorm (velocitySlice u t) 6 volume).toReal ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Space) 2 : ℝ) *
        (eLpNorm (fderiv ℝ (velocitySlice u t)) 2 volume).toReal := by
  exact NavierStokesR3.RieszTestOperators.smooth_eLpNorm_six_toReal_le
    hsmooth h2 hD2

/-- The standard finite `L²`--`L⁶` interpolation bound at exponent `3`.

This is an ordinary interpolation statement for the same slice.  It does not
replace the spectral/fractional endpoint estimate required by Paper 1.
-/
theorem velocitySlice_memLp_three_interp
    {u : VelocityField} {t : ℝ}
    (h2 : MemLp (velocitySlice u t) 2 volume)
    (h6 : MemLp (velocitySlice u t) 6 volume) :
    MemLp (velocitySlice u t) 3 volume ∧
      comparisonLpNorm 3 (velocitySlice u t) ≤
        comparisonLpNorm 2 (velocitySlice u t) ^ (1 / 2 : ℝ) *
          comparisonLpNorm 6 (velocitySlice u t) ^ (1 / 2 : ℝ) := by
  have hmeas : AEStronglyMeasurable (velocitySlice u t) volume := h2.1
  have hbound := NavierStokesR3.WeightedInterpolation.memLp_and_lpNorm_le_rpow_mul
    (f := velocitySlice u t) (g := velocitySlice u t) (h := velocitySlice u t)
    (p := (2 : ℝ≥0∞)) (q := (6 : ℝ≥0∞)) (r := (3 : ℝ≥0∞))
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) h2 h6 hmeas
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
    (Filter.Eventually.of_forall (fun x => by
      have hx : 0 ≤ ‖velocitySlice u t x‖ := norm_nonneg _
      have hEq :
          ‖velocitySlice u t x‖ ^ (1 / 2 : ℝ) *
              ‖velocitySlice u t x‖ ^ (1 / 2 : ℝ) =
            ‖velocitySlice u t x‖ := by
        rw [← Real.rpow_add' hx (by norm_num)]
        norm_num
      exact hEq.ge
      ))
  simpa using hbound

end NSFormalization.Paper1
