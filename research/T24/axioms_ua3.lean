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

/-!
## Nonzero admissible witness (Ua3 / Ua7 core)

The nonzero admissible perturbation `bWitness := spatialCurl A` and its three
public results

* `BlowupDensity.T24.NonzeroProbe.bWitness_admissible`
* `BlowupDensity.T24.NonzeroProbe.bWitness_ne_zero`
* `BlowupDensity.T24.NonzeroProbe.nonzero_admissible_momentum`

live in `research/T24/probes/affine_momentum_nonzero.lean`, which is a standalone
`lake env lean` probe (it imports `Contracts.*`/`Bindings.*` and is therefore not
a library module this file can `import`).  Its axioms are audited by the
`#print axioms` block at the foot of that probe; each prints exactly
`[propext, Classical.choice, Quot.sound]`.  Verify with
`lake env lean ../research/T24/probes/affine_momentum_nonzero.lean`.
-/
