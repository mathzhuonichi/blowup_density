import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith

/-! Real-power decay underlying the force and trajectory limits in Paper 1.
These prove convergence of the actual scalar bounds, not the unformalized
spatial change-of-variables estimates that produce those bounds. -/
namespace NSFormalization.Paper1
open Filter Topology

/-- The two terms in the subcritical Sobolev insertion estimate vanish together. -/
theorem sobolev_error_tendsto_zero (s C : ℝ) (hs : s < (1 : ℝ) / 2) :
    Tendsto (fun ε : ℝ => C * (ε ^ ((1 : ℝ) / 2 - s) +
      ε ^ ((3 : ℝ) / 2 - s))) (𝓝 0) (𝓝 0) := by
  have h₁ := tendsto_id.rpow_const_nhds_zero (by linarith : 0 < (1 : ℝ) / 2 - s)
  have h₂ := tendsto_id.rpow_const_nhds_zero (by linarith : 0 < (3 : ℝ) / 2 - s)
  simpa using (h₁.add h₂).const_mul C

/-- Energy and dissipation error tends to zero at the specified packet rates. -/
theorem energy_error_tendsto_zero (M D C : ℝ) :
    Tendsto (fun ε : ℝ => (M + D) * ε ^ ((1 : ℝ) / 2) +
      C * ε ^ ((3 : ℝ) / 2)) (𝓝 0) (𝓝 0) := by
  have h₁ := tendsto_id.rpow_const_nhds_zero (by norm_num : 0 < (1 : ℝ) / 2)
  have h₂ := tendsto_id.rpow_const_nhds_zero (by norm_num : 0 < (3 : ℝ) / 2)
  simpa using (h₁.const_mul (M + D)).add (h₂.const_mul C)

/-- The mixed-norm sufficient region is exactly positivity of this exponent. -/
def mixedExponent (pInv qInv : ℝ) : ℝ := -3 + 3 * pInv + 2 * qInv

theorem mixedExponent_pos_iff (pInv qInv : ℝ) :
    0 < mixedExponent pInv qInv ↔ 3 < 3 * pInv + 2 * qInv := by
  unfold mixedExponent
  constructor <;> intro h <;> linarith

/-- Reciprocal exponents represent infinite Lebesgue endpoints by zero. -/
theorem mixed_error_tendsto_zero (pInv qInv C : ℝ)
    (h : 3 < 3 * pInv + 2 * qInv) :
    Tendsto (fun ε : ℝ => C * (ε ^ mixedExponent pInv qInv +
      ε ^ (mixedExponent pInv qInv + 1))) (𝓝 0) (𝓝 0) := by
  have ha := (mixedExponent_pos_iff pInv qInv).mpr h
  have h₁ := tendsto_id.rpow_const_nhds_zero ha
  have h₂ := tendsto_id.rpow_const_nhds_zero (by linarith : 0 < mixedExponent pInv qInv + 1)
  simpa using (h₁.add h₂).const_mul C

end NSFormalization.Paper1
