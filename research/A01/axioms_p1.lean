import NSFormalization.Section4.A01.RadialPotential

/-! Axiom audit for A01 unit P1 (`RadialPotential.lean`).
Every public declaration must depend only on `propext`, `Classical.choice`,
`Quot.sound`. -/

open NSFormalization.Section4.A01.RadialPotential

#print axioms inner_fderiv_symm
#print axioms hasFDerivAt_radialPotential
#print axioms pressureGradient_pressurePotential
