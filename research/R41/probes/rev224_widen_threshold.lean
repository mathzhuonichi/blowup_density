import NSFormalization.Section4.R41.NonDensityL1
noncomputable section
open scoped ENNReal
open NSFormalization.Section4
open A02 (SpaceTimeField)
open D01 R41
namespace Review224
-- Positive controls: ambient centre and all numerical hypotheses.
example : (0 : SpaceTimeField) ∈ forceClassR := zero_mem_forceClassR
example : (0 : ℝ) < 1 ∧ (0 : ℝ) < 1 ∧ (1 / 2 : ℝ) ≤ 1 / 2 := by norm_num
example : ¬ BreakdownDenseR 1 (fun _ => 0) 1 1 (1 / 2) :=
  not_breakdownDenseR_zero_L1 1 1 (by norm_num) (by norm_num) _ le_rfl
-- MUTATION: widen the order range from [1/2, ∞) to [0, ∞).
-- The proof is copied unchanged, with every original argument retained.
theorem widened_criticalRadius {ν T s : ℝ} (hν : 0 < ν)
    (hs : 0 ≤ s) {f : SpaceTimeField} (hf : f ∈ breakdownSetRZero ν T) :
    ENNReal.ofReal (R43.criticalConst * ν) ≤ forceSobolevENorm 1 s f := by
  have hhalf : ENNReal.ofReal (R43.criticalConst * ν) ≤ forceSobolevENormL1 (1 / 2) f := by
    apply le_of_not_gt
    intro hsmall
    have htop := R43.inhomogeneousAtZero_of_memForceR ν hν f hf.1 hsmall
    exact ENNReal.ofReal_ne_top (top_le_iff.mp (htop ▸ hf.2))
  exact hhalf.trans (forceSobolevENorm_mono_order 1 (1 / 2) s hs f)

end Review224
