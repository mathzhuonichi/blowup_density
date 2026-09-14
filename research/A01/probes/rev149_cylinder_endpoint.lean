import NSFormalization.Section4.A01.AprioriRows

/-! Reviewer probe for lane 149, brief item 1 ("what the consumer `HasAprioriBound` actually
provides/needs"): `HasAprioriBound` (`Horizon.lean:106`) asks for the **ContinuousMap sup-norm**
`‖u‖` over the *closed* `Icc 0 T`.  At the cylinder level the `Ico → Icc` endpoint is free: `u` is
a `ContinuousMap`, so a bound on the half-open window closes at `t = T` by continuity.  Hence the
endpoint that the consumer needs does **not** have to be paid on the energy side. -/

noncomputable section
namespace Rev149CylEnd
open Set Filter Topology

set_option autoImplicit false in
theorem contMap_norm_le_of_Ico {T R : ℝ} (hT : 0 < T) {X : Type*} [NormedAddCommGroup X]
    (u : C(Icc (0 : ℝ) T, X)) (hR : 0 ≤ R)
    (h : ∀ t : Icc (0 : ℝ) T, (t : ℝ) < T → ‖u t‖ ≤ R) : ‖u‖ ≤ R := by
  rw [ContinuousMap.norm_le _ hR]
  intro t
  rcases lt_or_eq_of_le t.2.2 with hlt | heq
  · exact h t hlt
  · -- the endpoint `t = T`: approximate from inside and use continuity of `s ↦ ‖u s‖`
    have hmemT : (T : ℝ) ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
    have hteq : t = (⟨T, hmemT⟩ : Icc (0 : ℝ) T) := Subtype.ext heq
    subst hteq
    set x : ℕ → ℝ := fun n => T - T / (n + 2) with hx
    have hxmem : ∀ n, x n ∈ Icc (0 : ℝ) T := by
      intro n
      constructor
      · have h1 : T / (n + 2) ≤ T := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [hT.le, Nat.cast_nonneg (α := ℝ) n]
        simpa [hx] using h1
      · have : 0 ≤ T / (n + 2) := by positivity
        simpa [hx] using this
    have hxlt : ∀ n, x n < T := by
      intro n
      have : 0 < T / (n + 2) := by positivity
      simpa [hx] using this
    have hxtend : Tendsto x atTop (𝓝 T) := by
      have hd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun n : ℕ => T / ((n : ℝ) + 2)) atTop (𝓝 0) := hd.const_div_atTop T
      have h2 : Tendsto (fun n : ℕ => T - T / ((n : ℝ) + 2)) atTop (𝓝 (T - 0)) :=
        (tendsto_const_nhds (x := T) (f := atTop)).sub h1
      simpa [hx] using h2
    have hsub : Tendsto (fun n => (⟨x n, hxmem n⟩ : Icc (0 : ℝ) T)) atTop
        (𝓝 (⟨T, hmemT⟩ : Icc (0 : ℝ) T)) := tendsto_subtype_rng.mpr hxtend
    have hcont : Tendsto (fun n => ‖u ⟨x n, hxmem n⟩‖) atTop (𝓝 ‖u ⟨T, hmemT⟩‖) :=
      ((continuous_norm.comp u.continuous).tendsto _).comp hsub
    refine le_of_tendsto hcont (Eventually.of_forall fun n => ?_)
    exact h ⟨x n, hxmem n⟩ (hxlt n)

end Rev149CylEnd
