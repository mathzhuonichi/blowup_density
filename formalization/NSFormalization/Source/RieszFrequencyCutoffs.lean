import NSFormalization.Source.RieszSchwartzPairing
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! The actual singular frequency symbol split into its L2 near part and
bounded far part. These are cutoff functions, not smooth temperate multipliers. -/
noncomputable section
namespace NSFormalization.RieszFrequencyCutoffs
open MeasureTheory Set Metric
open scoped ENNReal
abbrev Space := EuclideanSpace ℝ (Fin 3)

def symbol (a : ℝ) (x : Space) : ℂ := (‖x‖ ^ (-a) : ℝ)
def low (a : ℝ) : Space → ℂ := (ball 0 1).indicator (symbol a)
def high (a : ℝ) : Space → ℂ := (ball 0 1)ᶜ.indicator (symbol a)

theorem measurable_symbol (a : ℝ) : Measurable (symbol a) := by
  unfold symbol
  fun_prop

theorem low_memLp {a : ℝ} (ha : a < 3/2) : MemLp (low a) 2 volume := by
  rw [low, memLp_indicator_iff_restrict measurableSet_ball]
  apply (memLp_two_iff_integrable_sq_norm (measurable_symbol a).aestronglyMeasurable.restrict).mpr
  apply integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2*a)
    (by simp) (by simp; linarith)
  · filter_upwards with x
    have he : ‖symbol a x‖ ^ 2 = ‖x‖ ^ (-(2*a)) := by
      simp only [symbol, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [← Real.rpow_mul_natCast (norm_nonneg x)]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), he, one_mul]
  · exact ((measurable_symbol a).norm.pow_const 2).aestronglyMeasurable

theorem high_memLp {a : ℝ} (ha : 0 ≤ a) : MemLp (high a) ⊤ volume := by
  apply memLp_top_of_bound ((measurable_symbol a).indicator measurableSet_ball.compl).aestronglyMeasurable 1
  filter_upwards with x
  by_cases hx : x ∈ ball (0 : Space) 1
  · simp [hx]
  · have hx1 : 1 ≤ ‖x‖ := by simpa using hx
    simp only [indicator_of_mem (mem_compl hx), symbol, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hx1 (neg_nonpos.mpr ha)

theorem low_add_high (a : ℝ) (x : Space) : low a x + high a x = symbol a x := by
  by_cases hx : x ∈ ball (0 : Space) 1 <;> simp [low, high, hx]

end NSFormalization.RieszFrequencyCutoffs
