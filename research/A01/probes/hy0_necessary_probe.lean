import NSFormalization.Section4.A01.Propagation

/-!
Statement-level refutation that `gronwall_bddAbove_Ico`'s hypothesis `0 ≤ y 0` is
NECESSARY (lane 122 review, finding F4).  Per `logs/LESSONS.md` (2026-09-14), an
arithmetic proof-step counterexample does not prove a hypothesis necessary; this
refutes the whole lemma with `hy0` deleted.

Witness (reviewer's): `T₀ = 2`, `Cgron = 1`, `k = 1`, `b = 0`, `Kbnd = 2`,
`Bbnd = 0`, and `y = fun s => -Real.exp s` — the exact solution of `y' = y`,
`y 0 = -1`.  Then `hstep` holds with EQUALITY, every other hypothesis holds, yet
at `t = 0` the conclusion reads `-1 ≤ -exp 2`, which is false (`exp 2 ≥ 3`).

Check: `cd verification && lake env lean ../research/A01/probes/hy0_necessary_probe.lean`.
-/

open Set intervalIntegral MeasureTheory

namespace A01Hy0Probe

/-- `gronwall_bddAbove_Ico` with the `0 ≤ y 0` hypothesis DELETED. -/
def NoNonnegInitial : Prop :=
  ∀ {T₀ Cgron Kbnd Bbnd : ℝ} {y k b : ℝ → ℝ},
    0 ≤ Cgron →
    ContinuousOn y (Ico 0 T₀) → ContinuousOn k (Ico 0 T₀) → ContinuousOn b (Ico 0 T₀) →
    (∀ t ∈ Ico 0 T₀, 0 ≤ k t) → (∀ t ∈ Ico 0 T₀, 0 ≤ b t) →
    (∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, k s) ≤ Kbnd) →
    (∀ t ∈ Ico 0 T₀, (∫ s in (0 : ℝ)..t, b s) ≤ Bbnd) →
    (∀ t ∈ Ico 0 T₀, y t ≤ y 0 + ∫ s in (0 : ℝ)..t, (Cgron * k s * y s + b s)) →
    ∀ t ∈ Ico 0 T₀, y t ≤ (y 0 + Bbnd) * Real.exp (Cgron * Kbnd)

theorem hy0_is_necessary : ¬ NoNonnegInitial := by
  intro h
  have hmem0 : (0 : ℝ) ∈ Ico (0 : ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have H0 := h (T₀ := 2) (Cgron := 1) (Kbnd := 2) (Bbnd := 0)
    (y := fun s => -Real.exp s) (k := fun _ => 1) (b := fun _ => 0)
    zero_le_one
    (Real.continuous_exp.neg.continuousOn)
    continuousOn_const continuousOn_const
    (fun _ _ => zero_le_one) (fun _ _ => le_refl 0)
    (fun t ht => by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, mul_one, sub_zero]
      exact ht.2.le)
    (fun _ _ => by simp)
    (fun t _ => by
      -- hstep with equality: y t = y 0 + ∫₀ᵗ (1·1·y + 0), via FTC on `-exp`.
      have hfun : (fun s => 1 * 1 * (-Real.exp s) + 0) = fun s => -Real.exp s := by
        funext s; ring
      have hderiv : ∀ x ∈ uIcc (0 : ℝ) t, HasDerivAt (fun s => -Real.exp s) (-Real.exp x) x :=
        fun x _ => (Real.hasDerivAt_exp x).neg
      have hint : IntervalIntegrable (fun s => -Real.exp s) volume 0 t :=
        (Real.continuous_exp.neg).intervalIntegrable 0 t
      have hcalc : (∫ s in (0 : ℝ)..t, (1 * 1 * (-Real.exp s) + 0)) = -Real.exp t + Real.exp 0 := by
        rw [hfun, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]; ring
      rw [hcalc]; simp [Real.exp_zero])
    0 hmem0
  -- H0 : -exp 0 ≤ (-exp 0 + 0) * exp (1 * 2), i.e. -1 ≤ -exp 2.
  simp only [Real.exp_zero, add_zero, one_mul] at H0
  nlinarith [Real.add_one_le_exp (2 : ℝ), H0]

#print axioms hy0_is_necessary

end A01Hy0Probe
