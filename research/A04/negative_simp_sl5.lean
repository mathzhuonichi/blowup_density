import NSFormalization.Section4.A04.NonlinearBound

/-!
# Negative checks for the SL5 cluster (lane 118, SIMP-A04-nonlinear)

Companion to `research/A04/ATTEMPTS_SIMP.md` §"Lane 118 — SL5 cluster".  Demonstrates that
the hypotheses of the SL5 exports are load-bearing.

* **Route (i)** — the three `example : ¬ (…)` below PROVE a weakened statement false with a
  concrete counterexample (all elaborate; this file is silent under `lake env lean`):
  - `advection_eq_sum_partialDeriv_outerColumn` with the divergence-free hypothesis dropped;
  - `sum_inner_le_sqrt_mul_sqrt` / `abs_sum_inner_le_sqrt_mul_sqrt` with the second ℓ² factor
    dropped from the Cauchy–Schwarz bound.
* **Route (ii)** — the witness-heavy exports (`advection_slice_datum_eq`, `inner_advection_bound`,
  and the `hdiff` variant of the divergence form) require a `ClassicalSolutionR` / `SmoothL2` /
  nowhere-differentiable field witness to refute concretely, which is out of scope for a SIMP lane.
  Their weakened statements are recorded as `Prop`s (e.g. `weak_advection_drop_hdiff`); `exact?` /
  `simp` fail on them (transcript pasted in ATTEMPTS_SIMP.md).
* **Non-vacuity** — the final `example` inhabits AdvectionDivergence's hypothesis class with a
  *non-zero* field.
-/

open NavierStokes.ProblemStatement
open NSFormalization.Section4.A01 (convectionDivergence convectionDivergence_eq_advection_add_smul_div)
open NSFormalization.Section4.A03 (partialDeriv outerColumn)
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section4.A04

noncomputable section

/-! ## Route (i): concrete refutations -/

set_option autoImplicit false in
/-- **AdvectionDivergence `advection_eq_sum_partialDeriv_outerColumn`, `hdiv` dropped — FALSE.**
Counterexample: the velocity equal to spatial position, `u(t,x)=x`.  It is smooth (so `hdiff`
holds) but has `∇·u = 3 ≠ 0`, and the Leibniz identity `∇·(u⊗u)=(u·∇)u+(∇·u)•u`
(`convectionDivergence_eq_advection_add_smul_div`) then makes the two sides differ by `3•x ≠ 0`. -/
example : ¬ (∀ (u : SpaceTimeField) (t : ℝ),
    (∀ x, DifferentiableAt ℝ (fun y => u (t, y)) x) →
    (fun x => advection u t x)
      = fun x => ∑ j : Fin 3,
          partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) x) := by
  intro W
  set u : SpaceTimeField := fun p => p.2 with hu
  have hfun : (fun y : Space => u (0, y)) = fun y : Space => y := rfl
  have hdiff : ∀ x, DifferentiableAt ℝ (fun y : Space => u (0, y)) x := by
    rw [hfun]; exact fun x => differentiableAt_id
  have H := congrFun (W u 0 hdiff) (coordinateVector 0)
  rw [← convectionDivergence_eq_sum_partialDeriv_outerColumn u 0 (coordinateVector 0),
      convectionDivergence_eq_advection_add_smul_div u 0 (coordinateVector 0) (hdiff _)] at H
  have hcancel : spatialDivergence u 0 (coordinateVector 0) • u (0, coordinateVector 0) = 0 := by
    have h2 := H
    nth_rewrite 1 [← add_zero (advection u 0 (coordinateVector 0))] at h2
    exact (add_left_cancel h2).symm
  have hdiv3 : spatialDivergence u 0 (coordinateVector 0) = 3 := by
    simp only [spatialDivergence, spatialDerivative, hfun, fderiv_fun_id,
      ContinuousLinearMap.id_apply, coordinateVector]
    simp
  have huval : u (0, coordinateVector 0) = coordinateVector 0 := rfl
  rw [hdiv3, huval] at hcancel
  have hc0 : ((3 : ℝ) • coordinateVector 0) 0 = (0 : Space) 0 := by rw [hcancel]
  simp [coordinateVector] at hc0

set_option autoImplicit false in
/-- **NonlinearPairing `sum_inner_le_sqrt_mul_sqrt`, second ℓ² factor dropped — FALSE.**
On `E = ℝ`, `a ≡ 1`, `b ≡ 2` over `ι = Unit`: `∑⟪a,b⟫ = 2` but `√(∑‖a‖²) = 1`. -/
example : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type} (s : Finset ι) (a b : ι → E),
    ∑ j ∈ s, (inner ℝ (a j) (b j) : ℝ) ≤ Real.sqrt (∑ j ∈ s, ‖a j‖ ^ 2)) := by
  intro W
  have h := W (E := ℝ) (ι := Unit) Finset.univ (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ))
  simp at h

set_option autoImplicit false in
/-- **NonlinearPairing `abs_sum_inner_le_sqrt_mul_sqrt`, second ℓ² factor dropped — FALSE.**
Same counterexample: `|∑⟪a,b⟫| = 2 > 1 = √(∑‖a‖²)`. -/
example : ¬ (∀ {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type} (s : Finset ι) (a b : ι → E),
    |∑ j ∈ s, (inner ℝ (a j) (b j) : ℝ)| ≤ Real.sqrt (∑ j ∈ s, ‖a j‖ ^ 2)) := by
  intro W
  have h := W (E := ℝ) (ι := Unit) Finset.univ (fun _ => (1 : ℝ)) (fun _ => (2 : ℝ))
  simp at h

/-! ## Route (ii): witness-heavy weakened statements (failing searches in ATTEMPTS_SIMP.md) -/

set_option autoImplicit false in
/-- Weakened AdvectionDivergence with `hdiff` dropped — **mathematically FALSE** (witness known, Lean
check TODO; `REVIEW_SIMP_SL5.md` §6).  Explicit witness `u(t,y) = ε(y₀) • (y₁, y₀, 1)` with `ε = sign`
is differentiable off the single plane `{y₀ = 0}`; there `fderiv` is junk `0`, so at `x = e₁` the LHS
`advection u t e₁ = 0` while the RHS (columns `u_j•u = U_j•U` polynomial, `ε² = 1`) is `(0,1,0) ≠ 0`.
`exact?` cannot close the raw goal; machine-checked refutation deferred (≈80–120 lines via the
unconditional `convectionDivergence_eq_sum_partialDeriv_outerColumn` bridge + A01's Leibniz lemma). -/
def weak_advection_drop_hdiff : Prop := ∀ (u : SpaceTimeField) (t : ℝ),
    (∀ x, spatialDivergence u t x = 0) →
    (fun x => advection u t x)
      = fun x => ∑ j : Fin 3,
          partialDeriv j (outerColumn (fun y => u (t, y)) (fun y => u (t, y)) j) x

/-! ## Non-vacuity -/

set_option autoImplicit false in
/-- **Non-vacuity of AdvectionDivergence's hypotheses.**  A *non-zero* field (the constant `e₀`)
satisfies both `hdiff` (smooth) and `hdiv` (`∇·u=0`), so `advection_eq_sum_partialDeriv_outerColumn`
is not vacuously true. -/
example : ∃ (u : SpaceTimeField) (t : ℝ),
    u (t, 0) ≠ 0 ∧
    (∀ x, DifferentiableAt ℝ (fun y => u (t, y)) x) ∧
    (∀ x, spatialDivergence u t x = 0) := by
  refine ⟨fun _ => coordinateVector 0, 0, ?_, ?_, ?_⟩
  · show coordinateVector 0 ≠ (0 : Space)
    have hn : ‖coordinateVector (0 : Fin 3)‖ = 1 := by simp [coordinateVector]
    intro h; rw [h, norm_zero] at hn; exact one_ne_zero hn.symm
  · exact fun x => differentiableAt_const _
  · intro x
    simp [spatialDivergence, spatialDerivative]

end
