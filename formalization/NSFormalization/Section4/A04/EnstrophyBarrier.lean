import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# P21 Route B, B3: a domain-independent enstrophy barrier

The revised article `paper/revised/sections/02-preliminaries.tex:153–156` states
`∫₀ˢ ‖u(t)‖²_H² dt < ∞`, “then it extends smoothly beyond S”.
The estimates here support the separate H¹-uniform restart obligation; they do
not assert a new displayed clause of that proposition. All functions are real.
-/

noncomputable section
open Set MeasureTheory
namespace NSFormalization.Section4.A04

/-- Integrating the differential inequality requires only integrability of Z,
not integrability of the derivative of Y. -/
theorem enstrophy_integrated_of_bound
    {c C K F M a b : ℝ} {Y Z : ℝ → ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hab : a ≤ b)
    (hY : ContinuousOn Y (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ Y t)
    (hZ : IntegrableOn Z (Icc a b))
    (hinit : Y a ≤ K) (hend : 0 ≤ Y b)
    (hbound : ∀ t ∈ Ioo a b, Y t ≤ M)
    (hineq : ∀ t ∈ Ioo a b, deriv Y t + c * Z t ≤ C * (1 + Y t)^3 + C * F) :
    (∫ t in a..b, Z t) ≤ (K + C * (1 + M)^3 * (b-a) + C * F * (b-a)) / c := by
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hY
    (fun t ht => (hd t ht).hasDerivAt.hasDerivWithinAt)
    ((continuousOn_const.integrableOn_Icc).sub (hZ.const_mul c))
    (fun t ht => show deriv Y t ≤ (C * (1 + M)^3 + C * F) - c * Z t from by
      have hp : (1 + Y t)^3 ≤ (1 + M)^3 := (Odd.strictMono_pow (by decide : Odd 3)).monotone (by linarith [hbound t ht])
      have := mul_le_mul_of_nonneg_left hp hC
      linarith [hineq t ht])
  have hzint : IntervalIntegrable Z volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hZ
  change Y b - Y a ≤ ∫ y in a..b, (C * (1 + M)^3 + C * F) - c * Z y at hi
  rw [intervalIntegral.integral_sub intervalIntegrable_const (hzint.const_mul c),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul] at hi
  apply (le_div_iff₀ hc).2
  nlinarith

end NSFormalization.Section4.A04
