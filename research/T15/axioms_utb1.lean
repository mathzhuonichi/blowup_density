import NSFormalization.Section3.T15.HaarBridge

/-!
Axiom audit for T15 U-TB1 (`NSFormalization.Section3.T15.HaarBridge`).
Every printed set must be exactly `[propext, Classical.choice, Quot.sound]`.
Run: `cd verification && lake env lean ../research/T15/axioms_utb1.lean`
-/

open NSFormalization.Section3.T15

#print axioms lintegral_enorm_torusLift
#print axioms eLpNorm_torusLift_restrict
#print axioms periodize_eq_of_mem_interior
#print axioms periodize_eventuallyEq_interior
#print axioms eLpNorm_periodize_restrict_eq
#print axioms eLpNorm_torusLift_periodize
#print axioms eLpNorm_gradientVector_eq_gradientENorm
#print axioms gradientENorm_restrict_eq
#print axioms eLpNorm_torusLift_spatialGradient_periodize
#print axioms eLpNorm_torusLift_periodize_slice
