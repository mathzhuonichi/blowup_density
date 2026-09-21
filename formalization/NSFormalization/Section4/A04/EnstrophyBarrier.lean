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

/-- Reciprocal-square comparison, including both endpoints. -/
theorem enstrophy_reciprocal_barrier
    {c C F a b : ℝ} {Y Z : ℝ → ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hF : 0 ≤ F) (hab : a ≤ b)
    (hY : ContinuousOn Y (Icc a b))
    (hd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ Y t)
    (hn : ∀ t ∈ Icc a b, 0 ≤ Y t)
    (hZ : ∀ t ∈ Ioo a b, 0 ≤ Z t)
    (hi : ∀ t ∈ Ioo a b, deriv Y t + c * Z t ≤ C * (1 + Y t)^3 + C * F) :
    1 / (1 + Y a)^2 - 2 * C * (1 + F) * (b-a) ≤ 1 / (1 + Y b)^2 := by
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

/-- Explicit uniform time and height, chosen before the interval and functions.
The proof chooses `d = 1 / (4*C*(1+F)*(1+K)^2)`. -/
theorem enstrophy_uniform_barrier {c C K F : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hK : 0 ≤ K) (hF : 0 ≤ F) :
    ∃ d > 0, ∃ M : ℝ, M = 2 * (1 + K) - 1 ∧
      ∀ (a S : ℝ) (Y Z : ℝ → ℝ), S ≤ d →
      ContinuousOn Y (Icc a (a+S)) →
      (∀ t ∈ Ioo a (a+S), DifferentiableAt ℝ Y t) →
      (∀ t ∈ Icc a (a+S), 0 ≤ Y t) → Y a ≤ K →
      (∀ t ∈ Ioo a (a+S), 0 ≤ Z t) →
      (∀ t ∈ Ioo a (a+S), deriv Y t + c * Z t ≤ C * (1+Y t)^3 + C * F) →
      ∀ t ∈ Icc a (a+S), Y t ≤ M := by
  let d := 1 / (4 * C * (1+F) * (1+K)^2)
  have hA : 0 < 1+K := by linarith
  have hG : 0 < 1+F := by linarith
  refine ⟨d, by dsimp [d]; positivity, 2*(1+K)-1, rfl, ?_⟩
  intro a S Y Z hS hY hd hn hinit hZ hi t ht
  have hsub : Icc a t ⊆ Icc a (a+S) := Icc_subset_Icc le_rfl ht.2
  have hosub : Ioo a t ⊆ Ioo a (a+S) := Ioo_subset_Ioo le_rfl ht.2
  have hr := enstrophy_reciprocal_barrier hc.le hC.le hF ht.1 (hY.mono hsub)
    (fun x hx => hd x (hosub hx)) (fun x hx => hn x (hsub hx))
    (fun x hx => hZ x (hosub hx)) (fun x hx => hi x (hosub hx))
  have hya : 0 < 1+Y a := by linarith [hn a (hsub (left_mem_Icc.mpr ht.1))]
  have hyt : 0 < 1+Y t := by linarith [hn t ht]
  have hstart : 1 / (1+K)^2 ≤ 1 / (1+Y a)^2 := by
    apply one_div_le_one_div_of_le (sq_pos_of_pos hya)
    nlinarith
  have htime : 2*C*(1+F)*(t-a) ≤ 1 / (2*(1+K)^2) := by
    calc
      _ ≤ 2*C*(1+F)*d := mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
      _ = _ := by dsimp [d]; field_simp; ring
  have hlow : 1 / (2*(1+K)^2) ≤ 1 / (1+Y t)^2 := by
    have heq : 1 / (1+K)^2 = 2 * (1 / (2*(1+K)^2)) := by field_simp
    linarith
  have hsquares : (1+Y t)^2 ≤ 2*(1+K)^2 := by
    have := (div_le_div_iff₀ (by positivity : 0 < 2*(1+K)^2) (sq_pos_of_pos hyt)).mp hlow
    nlinarith
  nlinarith [sq_nonneg (1+K)]

/-- Monotone passage to the right endpoint, in the nonnegative integral.
No measurability assumption is needed for this stronger formulation. -/
theorem enstrophy_endpoint_lintegral {a b : ℝ} {Z : ℝ → ℝ} {B : ℝ≥0∞}
    (h : ∀ s < b, (∫⁻ t in Ico a s, ENNReal.ofReal (Z t)) ≤ B) :
    (∫⁻ t in Ico a b, ENNReal.ofReal (Z t)) ≤ B := by
  let J := {q : ℚ // (q : ℝ) < b}
  have heq : (⋃ q : J, Ico a (q.val : ℝ)) = Ico a b := by
    ext t
    simp only [mem_iUnion, mem_Ico]
    constructor
    · rintro ⟨q, hat, htq⟩
      exact ⟨hat, htq.trans q.property⟩
    · rintro ⟨hat, htb⟩
      obtain ⟨q, htq, hqb⟩ := exists_rat_btwn htb
      exact ⟨⟨q, hqb⟩, hat, htq⟩
  rw [← heq, setLIntegral_iUnion_of_directed]
  · exact iSup_le fun q => h _ q.property
  · intro i j
    refine ⟨max i j, ?_, ?_⟩ <;>
      apply Ico_subset_Ico_right <;> exact_mod_cast (show _ ≤ max i j from by simp)

/-- Ordinary-integral endpoint version. Local integrability is explicit because
Lean's real integral is zero for a nonintegrable function. The conclusion also
proves integrability at the endpoint, as required by continuation criteria. -/
theorem enstrophy_endpoint_integral {a b B : ℝ} {Z : ℝ → ℝ}
    (hab : a ≤ b) (hB : 0 ≤ B) (hm : Measurable Z)
    (hn : ∀ t ∈ Ico a b, 0 ≤ Z t)
    (hi : ∀ s ∈ Ico a b, IntegrableOn Z (Icc a s))
    (hb : ∀ s ∈ Ico a b, (∫ t in a..s, Z t) ≤ B) :
    IntegrableOn Z (Icc a b) ∧ (∫ t in a..b, Z t) ≤ B := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ico a b)] Z :=
    (ae_restrict_mem measurableSet_Ico).mono hn
  have hl : (∫⁻ t in Ico a b, ENNReal.ofReal (Z t)) ≤ ENNReal.ofReal B := by
    apply enstrophy_endpoint_lintegral
    intro s hs
    by_cases has : a ≤ s
    · have hsi := (hi s ⟨has, hs⟩).mono_set Ico_subset_Icc_self
      have hsn : 0 ≤ᵐ[volume.restrict (Ico a s)] Z :=
        (ae_restrict_mem measurableSet_Ico).mono fun t ht => hn t ⟨ht.1, ht.2.trans hs⟩
      rw [← ofReal_integral_eq_lintegral_ofReal hsi hsn,
        integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le has]
      exact ENNReal.ofReal_le_ofReal (hb s ⟨has, hs⟩)
    · simp [Ico_eq_empty_of_le (le_of_not_ge has)]
  have hint : IntegrableOn Z (Ico a b) :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).mpr
      (hl.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨(integrableOn_Icc_iff_integrableOn_Ico).mpr hint, ?_⟩
  rw [intervalIntegral.integral_of_le hab, ← integral_Ico_eq_integral_Ioc,
    integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl).trans_eq (ENNReal.toReal_ofReal hB)

/-- Uniform barrier and dissipation on the same time window. -/
theorem enstrophy_uniform_barrier_and_dissipation {c C K F : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hK : 0 ≤ K) (hF : 0 ≤ F) :
    ∃ d > 0, ∃ M : ℝ, M = 2 * (1 + K) - 1 ∧
      ∀ (a S : ℝ) (Y Z : ℝ → ℝ), 0 ≤ S → S ≤ d →
      ContinuousOn Y (Icc a (a+S)) →
      (∀ t ∈ Ioo a (a+S), DifferentiableAt ℝ Y t) →
      (∀ t ∈ Icc a (a+S), 0 ≤ Y t) → Y a ≤ K →
      (∀ t ∈ Ioo a (a+S), 0 ≤ Z t) →
      IntegrableOn Z (Icc a (a+S)) →
      (∀ t ∈ Ioo a (a+S), deriv Y t + c * Z t ≤ C * (1+Y t)^3 + C * F) →
      (∀ t ∈ Icc a (a+S), Y t ≤ M) ∧
      (∫ t in a..a+S, Z t) ≤ (K + C*(1+M)^3*S + C*F*S) / c := by
  obtain ⟨d, hd, M, hM, h⟩ := enstrophy_uniform_barrier hc hC hK hF
  refine ⟨d, hd, M, hM, ?_⟩
  intro a S Y Z hS hSd hY hdY hn hinit hnZ hiZ hineq
  have hbound := h a S Y Z hSd hY hdY hn hinit hnZ hineq
  refine ⟨hbound, ?_⟩
  simpa only [add_sub_cancel_left] using enstrophy_integrated_of_bound hc hC.le
    (by linarith : a ≤ a+S) hY hdY hiZ hinit (hn _ ⟨by linarith, le_rfl⟩)
    (fun t ht => hbound t (Ioo_subset_Icc_self ht)) hineq

end NSFormalization.Section4.A04
