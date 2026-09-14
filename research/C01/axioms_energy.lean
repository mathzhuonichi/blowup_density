import NSFormalization.Section4.C01.EnergyIdentity

/-!
Axiom audit for lane 131 (C01 energy split), unit E0.

Both theorems of `Section4/C01/EnergyIdentity.lean` are pure real-inner-product
algebra, so the transitive axiom set must be exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`, no added axiom.

Run:  cd verification && lake env lean ../research/C01/axioms_energy.lean
-/

open NSFormalization.Section4.C01

#print axioms inner_energy_identity
#print axioms inner_energy_identity_deriv
