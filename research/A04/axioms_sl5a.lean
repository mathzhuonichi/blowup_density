import NSFormalization.Section4.A04.AdvectionDivergence

open NSFormalization.Section4.A04

-- Axiom audit for every public declaration of
-- `Section4/A04/AdvectionDivergence.lean` (SL5 row 5a).
-- Expected: only `propext`, `Classical.choice`, `Quot.sound`.
#print axioms convectionDivergence_eq_sum_partialDeriv_outerColumn
#print axioms advection_eq_sum_partialDeriv_outerColumn
#print axioms advection_slice_eq_sum_partialDeriv_outerColumn

/-
Captured output (lane 100, `lake env lean ../research/A04/axioms_sl5a.lean`,
2026-09-13), exit 0:

'NSFormalization.Section4.A04.convectionDivergence_eq_sum_partialDeriv_outerColumn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.advection_eq_sum_partialDeriv_outerColumn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
'NSFormalization.Section4.A04.advection_slice_eq_sum_partialDeriv_outerColumn'
  depends on axioms: [propext, Classical.choice, Quot.sound]
-/
