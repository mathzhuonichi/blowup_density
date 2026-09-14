/-
  Lane 142 (A01 unit A3-M2) — axiom + non-vacuity audit for
  `Section4/A01/GronwallInstance.lean`.

  Check:  cd verification && lake env lean ../research/A01/axioms_a3_m2.lean
  Expect: exit 0, every `#print axioms` = [propext, Classical.choice, Quot.sound].

  Non-vacuity is exhibited on the **zero solution** `zeroSol 1 : ClassicalSolutionR 1 0 0 1`
  (lane-117 reviewer appendix A, `research/D01/REVIEW_SL8_ASSEMBLY.md`; the smooth-path
  witness `path_zero` from `research/A04/REVIEW_ENERGY_HIGH.md` appendix) with `Kbnd := 0`:
  the zero velocity has `sobolevNormAt 2 · = 0`, so the order-2 integral cap holds with `0`,
  and both `highOrder_bddAbove_of_kbnd` and `highOrder_bddAbove_all_orders_of_kbnd` fire.  No
  nonzero classical solution exists in tree yet (that is the rest of A01), so `zeroSol` is the
  only inhabitant available; the whole hypothesis package (`0<ν`, `0∈initialClassR`,
  `MemForceR 0`, `MemL1Hm 0`, a `ClassicalSolutionR`, `HasSmoothSobolevPath`, `3≤m`,
  `0<T₀≤T`, the cap) is inhabited, so the hypotheses are not jointly unsatisfiable.
-/
import NSFormalization.Section4.A01.GronwallInstance

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01 (IsSobolevDatum sobolevENorm MemForceR)
open NSFormalization.Section4.A02 (ClassicalSolutionR initialClassR MemHInfty IsSolenoidal)
open NSFormalization.Section4.A04
  (sobolevNormAt sobolevENorm_eq Cgron HasSmoothSobolevPath MemL1Hm memL1Hm_of_memForceR
    forceSobolevENormL1)
open NSFormalization.Section4.A01 (highOrder_bddAbove_of_kbnd highOrder_bddAbove_all_orders_of_kbnd)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

noncomputable section

namespace Lane142

/-! ## 0. The zero solution and its data (lane-117/128 reviewer appendices, verbatim). -/

theorem datum_zero (s : ℝ) : IsSobolevDatum s (fun _ : Space => (0 : Space)) 0 := by
  intro i ψ; simp

/-- The zero solution with zero force on `[0,1)`. -/
def zeroSol (ν : ℝ) : ClassicalSolutionR ν 0 0 1 where
  velocity := 0
  pressure := 0
  horizon_pos := zero_lt_one
  velocity_smooth := contDiffOn_const
  pressure_smooth := contDiffOn_const
  initial := fun _ => rfl
  divergence := by intro t _ x; simp [spatialDivergence, spatialDerivative]
  momentum := by
    intro t _ x
    simp [NavierStokesR3.ProblemStatement.navierStokesResidual, temporalDerivative, advection,
      spatialDerivative, spatialLaplacian, pressureGradient]
  sobolev := fun m => ⟨fun _ => 0, continuousOn_const, fun t _ => datum_zero _⟩
  pressure_gradient := by intro t _; simp [pressureGradient]

theorem memForceR_zero : MemForceR (0 : VelocityField) := by
  refine ⟨contDiffOn_const, fun m => ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const, ?_, ?_⟩⟩
  · exact MemLp.zero
  · exact MemLp.zero

theorem zero_mem_initialClassR : (0 : Space → Space) ∈ initialClassR := by
  refine ⟨⟨contDiff_const, fun m => ⟨0, datum_zero (m : ℝ)⟩⟩, ?_⟩
  intro x
  simp [spatialDivergence, spatialDerivative]

theorem path_zero (ν : ℝ) : HasSmoothSobolevPath 1 (zeroSol ν).velocity := by
  intro m
  exact ⟨fun _ => 0, fun t _ => datum_zero _, contDiffOn_const⟩

/-- `sobolevNormAt` of the zero field vanishes at every order and time: the zero field is an
order-`s` datum with datum `0`, and `‖0‖ₑ.toReal = 0`. -/
theorem sobolevNormAt_zero (s : ℝ) (t : ℝ) : sobolevNormAt s (0 : VelocityField) t = 0 := by
  have hd : IsSobolevDatum s (fun x : Space => (0 : VelocityField) (t, x)) 0 := datum_zero s
  show (sobolevENorm s (fun x : Space => (0 : VelocityField) (t, x))).toReal = 0
  rw [sobolevENorm_eq hd]; simp

/-- The order-2 integral cap holds with `Kbnd := 0` on the zero solution. -/
theorem kbnd_zero :
    ∀ t ∈ Ico (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t, sobolevNormAt 2 (zeroSol 1).velocity s ^ 2) ≤ 0 := by
  intro t _
  have hz : ∀ s : ℝ, sobolevNormAt (2 : ℝ) (zeroSol 1).velocity s ^ 2 = 0 := by
    intro s
    rw [show sobolevNormAt (2 : ℝ) (zeroSol 1).velocity s
        = sobolevNormAt (2 : ℝ) (0 : VelocityField) s from rfl, sobolevNormAt_zero]
    ring
  simp only [hz, intervalIntegral.integral_zero, le_refl]

/-! ## 1. Non-vacuity of the two module exports on the zero solution. -/

/-- `highOrder_bddAbove_of_kbnd` is inhabited (zero solution, `m = 3`, `T₀ = 1`, `Kbnd = 0`). -/
theorem nonvac_highOrder_bddAbove_of_kbnd :
    ∀ t ∈ Ico (0 : ℝ) 1,
      sobolevNormAt ((3 : ℕ) : ℝ) (zeroSol 1).velocity t ≤
        (sobolevNormAt ((3 : ℕ) : ℝ) (zeroSol 1).velocity 0 +
            (forceSobolevENormL1 ((3 : ℕ) : ℝ) (0 : VelocityField)).toReal)
          * Real.exp (Cgron 3 1 * 0) :=
  highOrder_bddAbove_of_kbnd (ν := 1) (a := 0) (f := 0) (T := 1)
    one_pos zero_mem_initialClassR memForceR_zero (memL1Hm_of_memForceR memForceR_zero)
    (zeroSol 1) (path_zero 1) (m := 3) le_rfl (T₀ := 1) (Kbnd := 0) one_pos le_rfl kbnd_zero

/-- `highOrder_bddAbove_all_orders_of_kbnd` is inhabited (zero solution, `T₀ = 1`, `Kbnd = 0`). -/
theorem nonvac_highOrder_bddAbove_all_orders_of_kbnd :
    ∀ m : ℕ, 3 ≤ m →
      BddAbove ((fun t => sobolevNormAt (m : ℝ) (zeroSol 1).velocity t) '' Ico (0 : ℝ) 1) :=
  highOrder_bddAbove_all_orders_of_kbnd (ν := 1) (a := 0) (f := 0) (T := 1)
    one_pos zero_mem_initialClassR memForceR_zero (memL1Hm_of_memForceR memForceR_zero)
    (zeroSol 1) (path_zero 1) (T₀ := 1) (Kbnd := 0) one_pos le_rfl kbnd_zero

#print axioms highOrder_bddAbove_of_kbnd
#print axioms highOrder_bddAbove_all_orders_of_kbnd
#print axioms nonvac_highOrder_bddAbove_of_kbnd
#print axioms nonvac_highOrder_bddAbove_all_orders_of_kbnd

end Lane142
