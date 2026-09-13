import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# Absorbing the subquadratic cutoff errors

The constants are independent of both the radius and the localized
gradient. An error carrying one inverse radius retains that factor after
Young absorption.
-/

noncomputable section
namespace NavierStokes.R3EnergyAbsorption

open Set Filter
open scoped Topology

theorem absorb_rpow {p c ε : ℝ} (hp : 0 ≤ p) (hp₂ : p < 2) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → c * a ^ p ≤ ε * a ^ 2 + C := by
  have ht : Tendsto (fun a : ℝ => c * a ^ (p - 2)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show 0 < 2 - p by linarith)).const_mul c
    simpa only [neg_sub, mul_zero] using h
  obtain ⟨A, hA⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
  let B := max 1 A
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨c * B ^ p, mul_nonneg hc (Real.rpow_nonneg hB.le _), ?_⟩
  intro a ha
  by_cases hab : a ≤ B
  · have hle := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha hab hp) hc
    nlinarith [sq_nonneg a]
  · have hapos : 0 < a := hB.trans (lt_of_not_ge hab)
    have hb := (hA a ((le_max_right 1 A).trans (le_of_not_ge hab))).le
    have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg a)
    have he : a ^ (p - 2) * a ^ 2 = a ^ p := by
      rw [← Real.rpow_natCast a 2, ← Real.rpow_add hapos]
      congr 1
      norm_num
    rw [mul_assoc, he] at hm
    exact hm.trans (le_add_of_nonneg_right (mul_nonneg hc (Real.rpow_nonneg hB.le _)))

theorem shifted_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ (1 + b) ^ p * (a ^ p + 1) := by
  have hp' := Real.rpow_nonneg (show 0 ≤ 1 + b by linarith) p
  by_cases h : a ≤ 1
  · have he := Real.rpow_le_rpow (by positivity : 0 ≤ a + b) (add_le_add h (le_refl b)) hp
    exact he.trans (by nlinarith [Real.rpow_nonneg ha p])
  · have hmul : a + b ≤ (1 + b) * a := by nlinarith [le_of_not_ge h]
    have he := Real.rpow_le_rpow (by positivity : 0 ≤ a + b) hmul hp
    rw [Real.mul_rpow (by positivity) ha] at he
    exact he.trans (by nlinarith)

/-- Every combination of the `3/2`, linear, and constant errors arising in
the localized comparison can be absorbed uniformly for all radii ≥ 1. -/
theorem absorb_cutoff_errors {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R a : ℝ, 1 ≤ R → 0 ≤ a →
      c / R * (a ^ (3 / 2 : ℝ) + a + 1) ≤ ε * a ^ 2 + C / R := by
  obtain ⟨C₁, hC₁, h₁⟩ := absorb_rpow (p := 3 / 2) (c := c) (ε := ε / 2)
    (by norm_num) (by norm_num) hc (by positivity)
  obtain ⟨C₂, hC₂, h₂⟩ := absorb_rpow (p := 1) (c := c) (ε := ε / 2)
    (by norm_num) (by norm_num) hc (by positivity)
  refine ⟨C₁ + C₂ + c, by positivity, ?_⟩
  intro R a hR ha
  have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hb₁ := h₁ a ha
  have hb₂ := h₂ a ha
  rw [Real.rpow_one] at hb₂
  have he : c * (a ^ (3 / 2 : ℝ) + a + 1) ≤ ε * a ^ 2 + (C₁ + C₂ + c) := by
    nlinarith
  have hdiv := div_le_div_of_nonneg_right he hR'.le
  have hsmall : ε * a ^ 2 / R ≤ ε * a ^ 2 := div_le_self (by positivity) hR
  rw [add_div] at hdiv
  calc
    _ = c * (a ^ (3 / 2 : ℝ) + a + 1) / R := by ring
    _ ≤ ε * a ^ 2 / R + (C₁ + C₂ + c) / R := hdiv
    _ ≤ _ := add_le_add hsmall le_rfl

/-- Sobolev estimates may have a cutoff remainder inside the `L⁶` bound.
That remainder is harmless uniformly for all radii at least one. -/
theorem absorb_sobolev_errors {c S d ε : ℝ} (hc : 0 ≤ c) (hS : 0 ≤ S) (hd : 0 ≤ d)
    (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R A B : ℝ, 1 ≤ R → 0 ≤ A → 0 ≤ B →
      B ≤ S * (A + d / R) →
      c / R * (B ^ (3 / 2 : ℝ) + B + A + 1) ≤ ε * A ^ 2 + C / R := by
  let k := S ^ (3 / 2 : ℝ) * (1 + d) ^ (3 / 2 : ℝ)
  have hk : 0 ≤ k := mul_nonneg (Real.rpow_nonneg hS _) (Real.rpow_nonneg (by positivity) _)
  let k' := k + S + S * d + 2
  have hk' : 0 ≤ k' := by dsimp [k']; positivity
  obtain ⟨C, hC, hbound⟩ := absorb_cutoff_errors (mul_nonneg hc hk') hε
  refine ⟨C, hC, ?_⟩
  intro R A B hR hA hB hSob
  have hR' : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hBS : B ≤ S * (A + d) := hSob.trans
    (mul_le_mul_of_nonneg_left (add_le_add le_rfl (div_le_self hd hR)) hS)
  have hpow : B ^ (3 / 2 : ℝ) ≤ k * (A ^ (3 / 2 : ℝ) + 1) := by
    have h := Real.rpow_le_rpow hB hBS (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [Real.mul_rpow hS (by positivity)] at h
    exact h.trans ((mul_le_mul_of_nonneg_left (shifted_rpow hA hd (by norm_num : (0 : ℝ) ≤ 3 / 2))
      (Real.rpow_nonneg hS _)).trans_eq (by dsimp [k]; ring))
  have hpoly : B ^ (3 / 2 : ℝ) + B + A + 1 ≤ k' * (A ^ (3 / 2 : ℝ) + A + 1) := by
    have hp : 0 ≤ A ^ (3 / 2 : ℝ) := Real.rpow_nonneg hA _
    dsimp only [k']
    nlinarith [mul_nonneg hk hA, mul_nonneg hS hp, mul_nonneg (mul_nonneg hS hd) hp,
      mul_nonneg (mul_nonneg hS hd) hA]
  calc
    _ ≤ c / R * (k' * (A ^ (3 / 2 : ℝ) + A + 1)) :=
      mul_le_mul_of_nonneg_left hpoly (div_nonneg hc hR'.le)
    _ = (c * k') / R * (A ^ (3 / 2 : ℝ) + A + 1) := by ring
    _ ≤ _ := hbound R A hR hA

end NavierStokes.R3EnergyAbsorption
