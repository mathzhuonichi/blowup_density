import NSFormalization.Section3.T15.Bridges

/-!
# T15 U1 axiom audit

Every declaration introduced by the canonical bridge module is listed below.
The expected output for each `#print axioms` line is exactly
`[propext, Classical.choice, Quot.sound]` (up to Lean's display formatting).
-/

open NSFormalization.Section3.T15

#print axioms completedDense_eq_via
#print axioms completedDenseHomogeneous
#print axioms completedDenseHomogeneous_eq_via
#print axioms scaledStartTime
#print axioms scaledSourcePoint
#print axioms scaledVelocity
#print axioms scaledPressure
#print axioms scaledForce
#print axioms alphaT
#print axioms periodizedScaledVelocity
#print axioms periodizedScaledPressure
#print axioms periodizedScaledForce
#print axioms normalizedScaledPressure
#print axioms scaledVelocity_eq_parabolicVelocity
#print axioms scaledPressure_eq_parabolicPressure
#print axioms scaledForce_eq_parabolicForce
#print axioms alphaT_formula
#print axioms normalizedScaledPressure_formula
#print axioms periodize_eq_vendor
