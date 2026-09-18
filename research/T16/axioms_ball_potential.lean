import NSFormalization.Section3.T16.BallPotential

/-!
Axiom conformance for lane 351 (T16 Gap 1, `BallPotential.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`.
Run: `cd verification && lake env lean ../research/T16/axioms_ball_potential.lean`.
-/

open NSFormalization.Section3.T16

#print axioms curl_potential_of_segment
#print axioms curl_centeredPotential_of_segment
#print axioms timePotential_congr_segment
#print axioms contDiffOn_bumpSmul
#print axioms contDiff_bumpSmul_slice
#print axioms timePotential_contDiffOn_ball
#print axioms spatialCurl_timePotential_on_ball
#print axioms exists_potential_on_ball
