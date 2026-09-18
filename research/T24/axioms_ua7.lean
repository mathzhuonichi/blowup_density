import NSFormalization.Section3.T24.AffineFamily

/-!
# Axiom audit for T24a Ua7 (`AffineWitness.lean` + `AffineFamily.lean`)

Every declaration of the two new modules must print exactly
`[propext, Classical.choice, Quot.sound]`.

Run from `verification/` with
`lake env lean ../research/T24/axioms_ua7.lean`.
-/

open NSFormalization.Section3.T24

/-! ## `Section3/T24/AffineWitness.lean` -/

#print axioms AffineWitness.potential
#print axioms AffineWitness.curlBump
#print axioms AffineWitness.carrier
#print axioms AffineWitness.isCompact_carrier
#print axioms AffineWitness.potential_contDiff
#print axioms AffineWitness.tsupport_potential_subset
#print axioms AffineWitness.potential_hasCompactSupport
#print axioms AffineWitness.curlBump_contDiff
#print axioms AffineWitness.tsupport_curlBump_subset
#print axioms AffineWitness.curlBump_hasCompactSupport
#print axioms AffineWitness.curlBump_divergence_free
#print axioms AffineWitness.curlBump_eq_zero_of_notMem
#print axioms AffineWitness.curlBump_admissible
#print axioms AffineWitness.curl_component_one
#print axioms AffineWitness.curlBump_ne_zero

/-! ## `Section3/T24/AffineFamily.lean` -/

#print axioms AffineFamily.scale
#print axioms AffineFamily.scale_pos
#print axioms AffineFamily.scale_le_one
#print axioms AffineFamily.scale_succ
#print axioms AffineFamily.scale_antitone
#print axioms AffineFamily.centerOffset
#print axioms AffineFamily.ballRadius
#print axioms AffineFamily.ballRadius_pos
#print axioms AffineFamily.center
#print axioms AffineFamily.norm_e0
#print axioms AffineFamily.dist_center_self
#print axioms AffineFamily.dist_center_center
#print axioms AffineFamily.closedBall_subset_ball
#print axioms AffineFamily.radius_add_lt_of_lt
#print axioms AffineFamily.radius_add_lt
#print axioms AffineFamily.notMem_closedBall_of_ne
#print axioms AffineFamily.timeBump
#print axioms AffineFamily.timeBump_support
#print axioms AffineFamily.spaceBump
#print axioms AffineFamily.spaceBump_rOut
#print axioms AffineFamily.bFam
#print axioms AffineFamily.bFam_admissible
#print axioms AffineFamily.bFam_ne_zero
#print axioms AffineFamily.bFam_mem_ball_of_ne_zero
#print axioms AffineFamily.bFam_eq_zero_of_notMem_ball
#print axioms AffineFamily.bFam_linearIndependent
#print axioms infinite_dimensional
