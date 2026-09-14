/-
  Lane 142 (A01 unit A3-M2) — axiom + non-vacuity audit for
  `Section4/A01/GronwallInstance.lean`.

  Check:  cd verification && lake env lean ../research/A01/axioms_a3_m2.lean
  Expect: exit 0, every `#print axioms` = [propext, Classical.choice, Quot.sound].

  Lane 144 (MAINT) retarget: the inline zero-solution reconstruction that lived in §0 here
  (`datum_zero`, `zeroSol`, `memForceR_zero`, `zero_mem_initialClassR`, `path_zero`,
  `sobolevNormAt_zero`) is now landed once in `NSFormalization.Section4.A04.ZeroSolution` and
  imported below, so this file no longer rebuilds it.  `zeroSol` there is horizon-general
  (`zeroSol ν T (_ : 0 < ν) (hT : 0 < T) : ClassicalSolutionR ν 0 0 T`); the audit instantiates
  it at `ν = T = 1`.

  Non-vacuity is exhibited on the **zero solution** `zeroSol 1 1 one_pos one_pos :
  ClassicalSolutionR 1 0 0 1` with `Kbnd := 0`: the zero velocity has `sobolevNormAt 2 · = 0`, so
  the order-2 integral cap holds with `0`, and both `highOrder_bddAbove_of_kbnd` and
  `highOrder_bddAbove_all_orders_of_kbnd` fire.  No nonzero classical solution exists in tree yet
  (that is the rest of A01), so `zeroSol` is the only inhabitant available; the whole hypothesis
  package (`0<ν`, `0∈initialClassR`, `MemForceR 0`, `MemL1Hm 0`, a `ClassicalSolutionR`,
  `HasSmoothSobolevPath`, `3≤m`, `0<T₀≤T`, the cap) is inhabited, so the hypotheses are not
  jointly unsatisfiable.
-/
import NSFormalization.Section4.A01.GronwallInstance
import NSFormalization.Section4.A04.ZeroSolution

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Section4.D01 (IsSobolevDatum sobolevENorm MemForceR)
open NSFormalization.Section4.A02 (ClassicalSolutionR initialClassR MemHInfty IsSolenoidal)
open NSFormalization.Section4.A04
  (sobolevNormAt sobolevENorm_eq Cgron HasSmoothSobolevPath MemL1Hm memL1Hm_of_memForceR
    forceSobolevENormL1 zeroSol zeroSol_velocity memForceR_zero zero_mem_initialClassR path_zero
    sobolevNormAt_zero)
open NSFormalization.Section4.A01 (highOrder_bddAbove_of_kbnd highOrder_bddAbove_all_orders_of_kbnd)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ContDiff

noncomputable section

namespace Lane142

/-! ## 0. The zero solution and its data are now imported from `A04.ZeroSolution` (lane 144).

`zeroSol 1 1 one_pos one_pos : ClassicalSolutionR 1 0 0 1`, `memForceR_zero`,
`zero_mem_initialClassR`, `path_zero 1 1 one_pos one_pos` and `sobolevNormAt_zero` all come from
`NSFormalization.Section4.A04.ZeroSolution`; only the order-2 cap `kbnd_zero`, which is specific
to this audit, stays local. -/

/-- The order-2 integral cap holds with `Kbnd := 0` on the zero solution. -/
theorem kbnd_zero :
    ∀ t ∈ Ico (0 : ℝ) 1,
      (∫ s in (0 : ℝ)..t,
          sobolevNormAt 2 (zeroSol 1 1 one_pos one_pos).velocity s ^ 2) ≤ 0 := by
  intro t _
  have hz : ∀ s : ℝ,
      sobolevNormAt (2 : ℝ) (zeroSol 1 1 one_pos one_pos).velocity s ^ 2 = 0 := by
    intro s
    simp [zeroSol_velocity, sobolevNormAt_zero]
  simp only [hz, intervalIntegral.integral_zero, le_refl]

/-! ## 1. Non-vacuity of the two module exports on the zero solution. -/

/-- `highOrder_bddAbove_of_kbnd` is inhabited (zero solution, `m = 3`, `T₀ = 1`, `Kbnd = 0`). -/
theorem nonvac_highOrder_bddAbove_of_kbnd :
    ∀ t ∈ Ico (0 : ℝ) 1,
      sobolevNormAt ((3 : ℕ) : ℝ) (zeroSol 1 1 one_pos one_pos).velocity t ≤
        (sobolevNormAt ((3 : ℕ) : ℝ) (zeroSol 1 1 one_pos one_pos).velocity 0 +
            (forceSobolevENormL1 ((3 : ℕ) : ℝ) (0 : VelocityField)).toReal)
          * Real.exp (Cgron 3 1 * 0) :=
  highOrder_bddAbove_of_kbnd (ν := 1) (a := 0) (f := 0) (T := 1)
    one_pos zero_mem_initialClassR memForceR_zero (memL1Hm_of_memForceR memForceR_zero)
    (zeroSol 1 1 one_pos one_pos) (path_zero 1 1 one_pos one_pos) (m := 3) le_rfl (T₀ := 1)
    (Kbnd := 0) one_pos le_rfl kbnd_zero

/-- `highOrder_bddAbove_all_orders_of_kbnd` is inhabited (zero solution, `T₀ = 1`, `Kbnd = 0`). -/
theorem nonvac_highOrder_bddAbove_all_orders_of_kbnd :
    ∀ m : ℕ, 3 ≤ m →
      BddAbove ((fun t => sobolevNormAt (m : ℝ) (zeroSol 1 1 one_pos one_pos).velocity t) ''
        Ico (0 : ℝ) 1) :=
  highOrder_bddAbove_all_orders_of_kbnd (ν := 1) (a := 0) (f := 0) (T := 1)
    one_pos zero_mem_initialClassR memForceR_zero (memL1Hm_of_memForceR memForceR_zero)
    (zeroSol 1 1 one_pos one_pos) (path_zero 1 1 one_pos one_pos) (T₀ := 1) (Kbnd := 0)
    one_pos le_rfl kbnd_zero

#print axioms highOrder_bddAbove_of_kbnd
#print axioms highOrder_bddAbove_all_orders_of_kbnd
#print axioms nonvac_highOrder_bddAbove_of_kbnd
#print axioms nonvac_highOrder_bddAbove_all_orders_of_kbnd

end Lane142
