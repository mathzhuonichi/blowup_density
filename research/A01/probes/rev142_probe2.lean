-- Reviewer probe (lane 142 review, REVIEW_A3_M2.md), preserved verbatim; compiles on this branch.
/- Lane 142 review probe 2:
   (A) the Kbnd-free statement collapses (so `hkbnd` IS load-bearing);
   (B) `hkbnd` is satisfiable for ANY classical solution as soon as T₀ < T
       (the hole is a *value*, not a *possibility*). -/
import NSFormalization.Section4.A01.GronwallInstance

open Set MeasureTheory
open NSFormalization.Section4.A04
open NSFormalization.Section4.A01 (sobolevNormAt_nonneg highOrder_bddAbove_of_kbnd)
open NSFormalization.Section4.A02 (SpaceTimeField SpatialField ClassicalSolutionR initialClassR)
open NSFormalization.Section4.D01 (MemForceR)

noncomputable section
namespace Rev142

/-! ### (A) An upper bound valid for EVERY `Kbnd` forces the quantity to be `≤ 0`. -/
theorem exp_collapse {y A C : ℝ} (hC : 0 < C) (hA : 0 ≤ A)
    (h : ∀ K : ℝ, y ≤ A * Real.exp (C * K)) : y ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  rcases eq_or_lt_of_le hA with hA0 | hApos
  · have h0 := h 0
    rw [← hA0] at h0
    simp at h0
    linarith
  · have hpos : 0 < y / (2 * A) := div_pos hcon (by linarith)
    have hCK : C * (Real.log (y / (2 * A)) / C) = Real.log (y / (2 * A)) := by
      field_simp
    have hK := h (Real.log (y / (2 * A)) / C)
    rw [hCK, Real.exp_log hpos] at hK
    have hhalf : A * (y / (2 * A)) = y / 2 := by field_simp
    rw [hhalf] at hK
    linarith

/-- **`hkbnd` is load-bearing.**  If the lane's conclusion held for every `Kbnd`
(i.e. with the `hkbnd` hypothesis deleted and `Kbnd` left free), then the `H^m`
norm of the velocity would be identically zero on `[0,T₀)` — so the `Kbnd`-free
statement is false for any solution with a nonzero `H^m` norm. -/
theorem kbnd_free_collapses
    {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ} (hν : 0 < ν)
    (w : ClassicalSolutionR ν a f T) {m : ℕ} {T₀ : ℝ}
    (H : ∀ Kbnd : ℝ, ∀ t ∈ Ico (0 : ℝ) T₀,
        sobolevNormAt (m : ℝ) w.velocity t ≤
          (sobolevNormAt (m : ℝ) w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal)
            * Real.exp (Cgron m ν * Kbnd)) :
    ∀ t ∈ Ico (0 : ℝ) T₀, sobolevNormAt (m : ℝ) w.velocity t = 0 := by
  intro t ht
  have hA : 0 ≤ sobolevNormAt (m : ℝ) w.velocity 0 + (forceSobolevENormL1 (m : ℝ) f).toReal :=
    add_nonneg (sobolevNormAt_nonneg _ _ _) ENNReal.toReal_nonneg
  exact le_antisymm (exp_collapse (Cgron_pos m ν hν) hA (fun K => H K t ht))
    (sobolevNormAt_nonneg _ _ _)

/-! ### (B) `hkbnd` is satisfiable for every classical solution on every `T₀ < T`. -/
theorem kbnd_exists {ν : ℝ} {a : SpatialField} {f : SpaceTimeField} {T : ℝ}
    (w : ClassicalSolutionR ν a f T) {T₀ : ℝ} (_h0 : 0 ≤ T₀) (hT₀ : T₀ < T) :
    ∃ Kbnd : ℝ, ∀ t ∈ Ico (0 : ℝ) T₀,
      (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2) ≤ Kbnd := by
  have hsub : Icc (0 : ℝ) T₀ ⊆ Ico (0 : ℝ) T := fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hT₀⟩
  have hcont : ContinuousOn (fun s => sobolevNormAt 2 w.velocity s ^ 2) (Icc (0 : ℝ) T₀) :=
    ((continuousOn_sobolevNormAt_velocity w 2).mono hsub).pow 2
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max M 0 * T₀, ?_⟩
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have htT₀ : t ≤ T₀ := ht.2.le
  have huIcc : uIcc (0 : ℝ) t ⊆ Icc (0 : ℝ) T₀ := by
    rw [uIcc_of_le ht0]
    exact Icc_subset_Icc le_rfl htT₀
  have hint : IntervalIntegrable (fun s => sobolevNormAt 2 w.velocity s ^ 2) volume 0 t :=
    (hcont.mono huIcc).intervalIntegrable
  have hC0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  calc (∫ s in (0 : ℝ)..t, sobolevNormAt 2 w.velocity s ^ 2)
      ≤ ∫ _s in (0 : ℝ)..t, max M 0 := by
        refine intervalIntegral.integral_mono_on ht0 hint intervalIntegrable_const ?_
        intro s hs
        exact le_trans (le_trans (le_abs_self _) (hM s (huIcc (by rw [uIcc_of_le ht0]; exact hs))))
          (le_max_left _ _)
    _ = t * max M 0 := by simp
    _ ≤ T₀ * max M 0 := mul_le_mul_of_nonneg_right htT₀ hC0
    _ = max M 0 * T₀ := mul_comm _ _

end Rev142
