import NSFormalization.Section3.T13.Assembly

/-!
Axiom audit for lane 359 (T13 `localization` assembly + `LocalizationAPI`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
Run with: `cd verification && lake env lean ../research/T13/axioms_assembly.lean`.
-/

open NSFormalization.Section3.T13

-- §1 generic helpers
#print axioms enn_le_of_sq_le
#print axioms eLpNorm_two_sq

-- §2 periodize smoothness / periodicity
#print axioms latticeVector_eq_lattice
#print axioms periodize_eq_vendor
#print axioms contDiff_periodize_supported
#print axioms isPeriodicSpatial_periodize

-- §3 physical L² torus/cube identity
#print axioms lintegral_torusLift_normSq
#print axioms torus_cube_L2

-- §4-§5 the estimate and the record
#print axioms homogeneous_bound
#print axioms localization
#print axioms localizationAPI
