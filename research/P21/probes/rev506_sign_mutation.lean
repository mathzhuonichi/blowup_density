import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
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
open scoped ENNReal
namespace Rev506SignMutation

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

/-- Reciprocal-square comparison, including both endpoints. -/
theorem enstrophy_reciprocal_barrier
    {c C F a b : ℝ} {Y Z : ℝ → ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hF : 0 ≤ F) (hab : a ≤ b)
    (hY : ContinuousOn Y (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ Y t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ Y t)
    (hZ : ∀ t ∈ Ioo a b, 0 ≤ Z t)
    (hi : ∀ t ∈ Ioo a b, deriv Y t + c * Z t ≤ C * (1 + Y t)^3 + C * F) :
    1 / (1 + Y a)^2 + 2 * C * (1 + F) * (b-a) ≤ 1 / (1 + Y b)^2 := by
  have hp : ∀ t ∈ Icc a b, 0 < 1 + Y t := fun t ht => by linarith [hn t ht]
  have hcont : ContinuousOn (fun t => -(1 / (1 + Y t)^2)) (Icc a b) :=
    (continuousOn_const.div ((continuousOn_const.add hY).pow 2)
      (fun t ht => pow_ne_zero _ (ne_of_gt (hp t ht)))).neg
  have hder : ∀ t ∈ Ioo a b, HasDerivAt (fun t => -(1 / (1 + Y t)^2))
      (2 * deriv Y t / (1 + Y t)^3) t := by
    intro t ht
    convert! (((((hd t ht).hasDerivAt.const_add 1).pow 2).inv
      (pow_ne_zero _ (ne_of_gt (hp t (Ioo_subset_Icc_self ht))))).neg) using 1 <;>
      first | rfl | (funext x; simp [one_div]) | (simp only [Pi.pow_apply]; field_simp [ne_of_gt (hp t (Ioo_subset_Icc_self ht))]; ring)
  have hbound : ∀ t ∈ Ioo a b, 2 * deriv Y t / (1 + Y t)^3 ≤ 2 * C * (1 + F) := by
    intro t ht
    have hy := hn t (Ioo_subset_Icc_self ht)
    have hy3 : 1 ≤ (1 + Y t)^3 := by nlinarith [sq_nonneg (Y t)]
    have hcf : C * F ≤ C * F * (1 + Y t)^3 := le_mul_of_one_le_right (mul_nonneg hC hF) hy3
    have hz := mul_nonneg hc (hZ t ht)
    apply (div_le_iff₀ (pow_pos (hp t (Ioo_subset_Icc_self ht)) 3)).2
    nlinarith [hi t ht]
  have h := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hcont
    (fun t ht => (hder t ht).hasDerivWithinAt) continuousOn_const.integrableOn_Icc hbound
  rw [intervalIntegral.integral_const] at h
  simp only [smul_eq_mul] at h
  linarith


end Rev506SignMutation
