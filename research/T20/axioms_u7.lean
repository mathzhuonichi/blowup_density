import NSFormalization.Section3.T20.CriticalTrilinear

/-!
Axiom audit for T20 unit U7 (`Section3/T20/CriticalTrilinear.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
Run: `cd verification && lake env lean ../research/T20/axioms_u7.lean`
-/

open NSFormalization.Section3.T20

#print axioms NSFormalization.Section3.T20.aestronglyMeasurable_torusLift
#print axioms NSFormalization.Section3.T20.continuous_gradientTensor
#print axioms NSFormalization.Section3.T20.lintegral_enorm_mul_three_le_torus
#print axioms NSFormalization.Section3.T20.enorm_inner_advection_le
#print axioms NSFormalization.Section3.T20.criticalAdvectionHolderT
#print axioms NSFormalization.Section3.T20.criticalTrilinearConst
#print axioms NSFormalization.Section3.T20.criticalTrilinearConst_eq
#print axioms NSFormalization.Section3.T20.criticalTrilinearConst_pos
#print axioms NSFormalization.Section3.T20.criticalTrilinear_enorm
#print axioms NSFormalization.Section3.T20.criticalTrilinear
#print axioms NSFormalization.Section3.T20.periodicPairing_eq_integral_torusLift_inner
#print axioms NSFormalization.Section3.T20.criticalTrilinear_pairing
#print axioms NSFormalization.Section3.T20.advection_eq_slice
