import NSFormalization.Section3.T20.H1Trilinear

/-!
Axiom audit for T20 unit U10a (`Section3/T20/H1Trilinear.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
Run: `cd verification && lake env lean ../research/T20/axioms_u10a.lean`
-/

open NSFormalization.Section3.T20

#print axioms NSFormalization.Section3.T20.measurable_torusChartH1
#print axioms NSFormalization.Section3.T20.aestronglyMeasurable_torusLiftH1
#print axioms NSFormalization.Section3.T20.continuous_gradientTensorH1
#print axioms NSFormalization.Section3.T20.enorm_inner_advection_leH1
#print axioms NSFormalization.Section3.T20.lintegral_enorm_mul_three_le_torus_three_six_two
#print axioms NSFormalization.Section3.T20.h1AdvectionHolderT
#print axioms NSFormalization.Section3.T20.h1TrilinearConst
#print axioms NSFormalization.Section3.T20.h1TrilinearConst_pos
#print axioms NSFormalization.Section3.T20.h1Trilinear_enorm
#print axioms NSFormalization.Section3.T20.periodicLpENorm_two_laplacian_ne_top
#print axioms NSFormalization.Section3.T20.h1Trilinear_toReal
#print axioms NSFormalization.Section3.T20.h1Trilinear
#print axioms NSFormalization.Section3.T20.periodicPairing_eq_integral_torusLift_innerH1
#print axioms NSFormalization.Section3.T20.h1Trilinear_pairing
#print axioms NSFormalization.Section3.T20.advection_eq_sliceH1
#print axioms NSFormalization.Section3.T20.h1Trilinear_slice
