import NSFormalization.Section4.D01.DivergenceTime

/-!
Conformance check for D01 unit P2, sub-lemma SL4α: the time-derivative slice of a
classical whole-space solution is divergence-free
(`formalization/NSFormalization/Section4/D01/DivergenceTime.lean`).

Run with, from `verification/`:
  lake env lean ../research/D01/axioms_sl4a.lean

Every result must depend only on the standard logical axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

open NSFormalization.Section4.D01.DivergenceTime

-- SL4α: `div (∂ₜu)(t,·) = 0` on `Ioo 0 T`.
#print axioms spatialDivergence_temporalDerivative_eq_zero
-- The reproduced pure-Mathlib mixed-derivative helpers.
#print axioms spatial_fderiv_hasDerivAt
#print axioms fderiv_spatial_slice
#print axioms deriv_time_slice
