import NSFormalization.Section4.A01.ConvectionDivergence
import NSFormalization.Section4.A01.ProjectedEquation

/-!
Axiom audit for the A01 unit E1 modules (lane 093).
`lake env lean` this file from `verification/`; every public declaration must
report exactly `propext`, `Classical.choice`, `Quot.sound`.
-/

open NSFormalization.Section4.A01

#print axioms convectionDivergence
#print axioms convectionDivergence_eq_advection_add_smul_div
#print axioms convectionDivergence_eq_advection
#print axioms navierStokesResidual_eq_iff_projected
#print axioms projected_of_classicalSolution
