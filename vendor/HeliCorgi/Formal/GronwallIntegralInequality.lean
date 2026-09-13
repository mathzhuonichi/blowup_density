import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A Grönwall–Bellman integral inequality (T-SEL bridge lemma SEL-6)

The repository previously had **no** Grönwall infrastructure (bridge gap B1 of
`docs/gates/STAGE9_REVERSE_GAP_AUDIT_2026-09-02.md`, SS-1/SS-6).  This file supplies the
integral (Bellman) form consumed by the T-SEL bridge assembly:

if `y` is continuous on `[0, T]`, `m` is continuous and nonnegative there, and

`y t ≤ a + ∫ s in 0..t, m s * y s` for every `t ∈ [0, T]`,

then `y t ≤ a * exp (∫ s in 0..t, m s)` on `[0, T]`.

The proof is the classical one: the primitive `A t = a + ∫₀ᵗ m y` satisfies `y ≤ A`, is
differentiable at interior times with `A' = m y ≤ m A`, so `t ↦ A t · exp(−∫₀ᵗ m)` has
nonpositive interior derivative and is antitone on the closed interval by continuity;
evaluating at `0` gives the bound.

This is deliberately a standalone real-variable lemma: no PDE content, no carrier types.
The integral form is chosen so that the consumer needs **no** differentiability of
`t ↦ y t` — along a mild solution only continuity of the trajectory is certified.
-/

namespace MNS2

open MeasureTheory Set

noncomputable section

/-- **Grönwall–Bellman integral inequality** (T-SEL bridge lemma **SEL-6**).

If `y` is continuous on `[0, T]`, `m` is continuous and nonnegative on `[0, T]`, and
`y t ≤ a + ∫ s in 0..t, m s * y s` there, then `y t ≤ a * exp (∫ s in 0..t, m s)` on
`[0, T]`. -/
theorem le_mul_exp_of_le_add_intervalIntegral {T a : ℝ} {y m : ℝ → ℝ} (hT : 0 ≤ T)
    (hy : ContinuousOn y (Icc 0 T)) (hm : ContinuousOn m (Icc 0 T))
    (hm0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ m t)
    (hle : ∀ t ∈ Icc (0 : ℝ) T, y t ≤ a + ∫ s in (0 : ℝ)..t, m s * y s) :
    ∀ t ∈ Icc (0 : ℝ) T, y t ≤ a * Real.exp (∫ s in (0 : ℝ)..t, m s) := by
  have hmy : ContinuousOn (fun s => m s * y s) (Icc 0 T) := hm.mul hy
  -- interval integrability of both integrands up to every point of the horizon
  have hmyInt : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun s => m s * y s) volume 0 t := by
    intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    exact (hmy.mono hsub).intervalIntegrable_of_Icc ht.1
  have hmInt : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable m volume 0 t := by
    intro t ht
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc le_rfl ht.2
    exact (hm.mono hsub).intervalIntegrable_of_Icc ht.1
  -- continuity of the two primitives on the closed horizon
  have hAc : ContinuousOn (fun t => a + ∫ s in (0 : ℝ)..t, m s * y s) (Icc 0 T) := by
    refine continuousOn_const.add fun t _ => ?_
    refine intervalIntegral.continuousWithinAt_primitive (by simp) ?_
    rw [min_self, max_eq_right hT]
    exact hmyInt T (right_mem_Icc.mpr hT)
  have hMc : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, m s) (Icc 0 T) := by
    refine fun t _ => ?_
    refine intervalIntegral.continuousWithinAt_primitive (by simp) ?_
    rw [min_self, max_eq_right hT]
    exact hmInt T (right_mem_Icc.mpr hT)
  -- interior derivatives of the two primitives
  have hAder : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => a + ∫ s in (0 : ℝ)..r, m s * y s) (m t * y t) t := by
    intro t ht
    have hmem : Icc (0 : ℝ) T ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hct : ContinuousAt (fun s => m s * y s) t := hmy.continuousAt hmem
    have hsm : StronglyMeasurableAtFilter (fun s => m s * y s) (nhds t) volume :=
      ⟨Ioo (0 : ℝ) T, Ioo_mem_nhds ht.1 ht.2,
        (hmy.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo⟩
    exact (intervalIntegral.integral_hasDerivAt_right
      (hmyInt t ⟨ht.1.le, ht.2.le⟩) hsm hct).const_add a
  have hMder : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun r => ∫ s in (0 : ℝ)..r, m s) (m t) t := by
    intro t ht
    have hmem : Icc (0 : ℝ) T ∈ nhds t := Icc_mem_nhds ht.1 ht.2
    have hct : ContinuousAt m t := hm.continuousAt hmem
    have hsm : StronglyMeasurableAtFilter m (nhds t) volume :=
      ⟨Ioo (0 : ℝ) T, Ioo_mem_nhds ht.1 ht.2,
        (hm.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo⟩
    exact intervalIntegral.integral_hasDerivAt_right (hmInt t ⟨ht.1.le, ht.2.le⟩) hsm hct
  -- the comparison function `F t = A t · exp (−M t)` has nonpositive interior derivative
  have hFder : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt
        (fun r => (a + ∫ s in (0 : ℝ)..r, m s * y s) *
          Real.exp (-(∫ s in (0 : ℝ)..r, m s)))
        (m t * (y t - (a + ∫ s in (0 : ℝ)..t, m s * y s)) *
          Real.exp (-(∫ s in (0 : ℝ)..t, m s))) t := by
    intro t ht
    have h2 : HasDerivAt (fun r => Real.exp (-(∫ s in (0 : ℝ)..r, m s)))
        (Real.exp (-(∫ s in (0 : ℝ)..t, m s)) * -(m t)) t := ((hMder t ht).neg).exp
    have h3 := (hAder t ht).mul h2
    have heq : m t * (y t - (a + ∫ s in (0 : ℝ)..t, m s * y s)) *
        Real.exp (-(∫ s in (0 : ℝ)..t, m s)) =
        m t * y t * Real.exp (-(∫ s in (0 : ℝ)..t, m s)) +
          (a + ∫ s in (0 : ℝ)..t, m s * y s) *
            (Real.exp (-(∫ s in (0 : ℝ)..t, m s)) * -(m t)) := by
      ring
    rw [heq]
    exact h3
  have hFc : ContinuousOn
      (fun r => (a + ∫ s in (0 : ℝ)..r, m s * y s) *
        Real.exp (-(∫ s in (0 : ℝ)..r, m s))) (Icc 0 T) :=
    hAc.mul (Real.continuous_exp.comp_continuousOn hMc.neg)
  have hanti : AntitoneOn
      (fun r => (a + ∫ s in (0 : ℝ)..r, m s * y s) *
        Real.exp (-(∫ s in (0 : ℝ)..r, m s))) (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hFc ?_ ?_
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hFder t ht).differentiableAt).differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFder t ht).deriv]
      have htmem : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
      have h1 : 0 ≤ m t := hm0 t htmem
      have h2 : y t - (a + ∫ s in (0 : ℝ)..t, m s * y s) ≤ 0 :=
        sub_nonpos.mpr (hle t htmem)
      have h3 : 0 ≤ Real.exp (-(∫ s in (0 : ℝ)..t, m s)) := (Real.exp_pos _).le
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos h1 h2) h3
  -- evaluate the antitone comparison at the left endpoint and unwind
  intro t ht
  have hFt : (a + ∫ s in (0 : ℝ)..t, m s * y s) *
      Real.exp (-(∫ s in (0 : ℝ)..t, m s)) ≤
      (a + ∫ s in (0 : ℝ)..(0 : ℝ), m s * y s) *
        Real.exp (-(∫ s in (0 : ℝ)..(0 : ℝ), m s)) :=
    hanti (left_mem_Icc.mpr hT) ht ht.1
  have hF0 : (a + ∫ s in (0 : ℝ)..(0 : ℝ), m s * y s) *
      Real.exp (-(∫ s in (0 : ℝ)..(0 : ℝ), m s)) = a := by
    simp
  rw [hF0] at hFt
  have hexp : (0 : ℝ) < Real.exp (∫ s in (0 : ℝ)..t, m s) := Real.exp_pos _
  have hAle : a + ∫ s in (0 : ℝ)..t, m s * y s ≤
      a * Real.exp (∫ s in (0 : ℝ)..t, m s) := by
    have h := mul_le_mul_of_nonneg_right hFt hexp.le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
    exact h
  exact (hle t ht).trans hAle

end

end MNS2
