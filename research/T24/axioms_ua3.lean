import NSFormalization.Section3.T24.AffineMomentum

/-!
# T24a / Ua3 transitive-axiom audit

Run from `verification/` with
`lake env lean ../research/T24/axioms_ua3.lean`.
Every declaration below is expected to print exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms NSFormalization.Section3.T24.navierStokesResidual_affine_expand
#print axioms NSFormalization.Section3.T24.momentum
