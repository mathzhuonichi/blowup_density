import NSFormalization.Section3.T24.AffineForce

/-!
# T24a / Ua4 transitive-axiom audit

Run from `verification/` with
`lake env lean ../research/T24/axioms_ua4.lean`.
Every declaration below is expected to print exactly
`[propext, Classical.choice, Quot.sound]`.
-/

#print axioms NSFormalization.Section3.T24.affineCylinder_subset_interior
#print axioms NSFormalization.Section3.T24.affineCylinder_subset_positiveTimeDomain
#print axioms NSFormalization.Section3.T24.affineForce_eq_of_notMem_tsupport
#print axioms NSFormalization.Section3.T24.contDiffOn_affineForce_interior
#print axioms NSFormalization.Section3.T24.force_smooth
#print axioms NSFormalization.Section3.T24.tsupport_affineForce_subset
#print axioms NSFormalization.Section3.T24.force_support

/-!
## Probe declarations

`research/T24/probes/affine_force_closes.lean` (registered-vocabulary discharge on
`Bindings.packet ν hν`, plus the `b = 0` reduction) and
`research/T24/probes/affine_force_nonzero.lean` (the nonzero admissible witness
`bWitness = spatialCurl (θ·φ·e₁)` of lane 398, rebuilt, with both Ua4 conclusions
instantiated at it) import `Contracts.*`/`Bindings.*` and are therefore standalone
`lake env lean` probes, not library modules this file can `import`.  Each carries
its own `#print axioms` block; verify with

* `lake env lean ../research/T24/probes/affine_force_closes.lean`
* `lake env lean ../research/T24/probes/affine_force_nonzero.lean`
-/
