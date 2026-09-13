import NSFormalization.Section4.A04.HighEnergy
import NSFormalization.Section4.A04.TimeDerivative

/-!
Conformance / axiom audit for A04 unit G1 (the S-level core of eq:Rhigh) and its
sub-lemma SL1/D2.  Expected: only the standard logical axioms `propext`,
`Classical.choice`, `Quot.sound`.
Run: `cd verification && lake env lean ../research/A04/axioms_g1.lean`.
-/

open NSFormalization.Section4.A04

-- SL8 (arithmetic assembly to eq:Rhigh) and SL6 (tame transport)
#print axioms inner_energy_assembly
#print axioms inner_energy_Rhigh
#print axioms outerSobolevNormAt_le
#print axioms outerNormAt_le

-- SL1 / unit D2 (deriv G t is the datum of ∂ₜu(t,·))
#print axioms d2_scalar
#print axioms timeDeriv_isSobolevDatum
