import NSFormalization.Section4.A04.EnstrophyBarrier
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Set MeasureTheory
open NSFormalization.Section4.A04

-- Constant data and zero dissipation, with a common window before the datum.
example {c C K F : ℝ} (hc : 0 < c) (hC : 0 < C) (hK : 0 ≤ K) (hF : 0 ≤ F) :
    ∃ d > 0, ∀ a S y : ℝ, 0 ≤ S → S ≤ d → 0 ≤ y → y ≤ K →
      y ≤ 2*(1+K)-1 ∧
      (∫ _t in a..a+S, (0 : ℝ)) ≤ (K + C*(2*(1+K))^3*S + C*F*S)/c := by
  obtain ⟨d, hd, M, rfl, h⟩ := enstrophy_uniform_barrier_and_dissipation hc hC hK hF
  refine ⟨d, hd, ?_⟩
  intro a S y hS hSd hy hyK
  have hh := h a S (fun _ => y) (fun _ => 0) hS hSd continuousOn_const
    (fun _ _ => differentiableAt_const _) (fun _ _ => hy) hyK (fun _ _ => le_rfl)
    continuousOn_const.integrableOn_Icc (by
      intro t ht
      simp only [deriv_const, mul_zero, add_zero]
      positivity)
  exact ⟨hh.1 a ⟨le_rfl, by linarith⟩, by simpa using hh.2⟩

-- The actual unforced cubic ODE solution starting at zero.
noncomputable def cubicSolution (t : ℝ) : ℝ := (Real.sqrt (1-2*t))⁻¹ - 1

theorem cubicSolution_deriv {t : ℝ} (ht : t < 1/2) :
    HasDerivAt cubicSolution ((1+cubicSolution t)^3) t := by
  have hp : 0 < 1-2*t := by linarith
  have hn : Real.sqrt (1-2*t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have h := ((((hasDerivAt_id t).const_mul 2).const_sub 1).sqrt (ne_of_gt hp)).inv hn
  convert! h.sub_const 1 using 1
  dsimp [cubicSolution]
  field_simp
  ring

example : ∃ d > 0, ∀ S : ℝ, 0 ≤ S → S ≤ min d (1/4) →
    ∀ t ∈ Icc 0 S, cubicSolution t ≤ 1 := by
  obtain ⟨d, hd, M, hM, h⟩ := enstrophy_uniform_barrier
    (c := 1) (C := 1) (K := 0) (F := 0) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  norm_num at hM
  subst M
  refine ⟨d, hd, ?_⟩
  intro S hS hSd
  have hsmall : S ≤ 1/4 := hSd.trans (min_le_right _ _)
  have hp : ∀ t ∈ Icc 0 (0+S), 0 < 1-2*t := fun t ht => by linarith [ht.2]
  have hc : ContinuousOn cubicSolution (Icc 0 (0+S)) := by
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.inv₀
    · fun_prop
    · intro t ht
      exact ne_of_gt (Real.sqrt_pos.mpr (hp t ht))
  have hn : ∀ t ∈ Icc 0 (0+S), 0 ≤ cubicSolution t := by
    intro t ht
    have hspos := Real.sqrt_pos.mpr (hp t ht)
    have hsle : Real.sqrt (1-2*t) ≤ 1 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · linarith [ht.1]
    dsimp [cubicSolution]
    have : 1 ≤ (Real.sqrt (1-2*t))⁻¹ := (one_le_inv₀ hspos).mpr hsle
    linarith
  have hh := h 0 S cubicSolution (fun _ => 0) (hSd.trans (min_le_left _ _)) hc
    (fun t ht => (cubicSolution_deriv (by linarith [ht.2])).differentiableAt) hn
    (by norm_num [cubicSolution]) (fun _ _ => le_rfl) (by
      intro t ht
      rw [(cubicSolution_deriv (by linarith [ht.2])).deriv]
      simp)
  simpa using hh

-- Endpoint passage genuinely returns integrability, not just a totalized integral.
example {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc a b) ∧
      (∫ _t in a..b, (0 : ℝ)) ≤ 0 := by
  apply enstrophy_endpoint_integral hab (le_refl 0) measurable_const
  · simp
  · intro s hs
    exact continuousOn_const.integrableOn_Icc
  · simp
