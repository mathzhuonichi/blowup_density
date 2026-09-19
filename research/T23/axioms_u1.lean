import NSFormalization.Section3.T23.Placement

/-!
# T23 U1 axiom audit

Every public declaration introduced by the cube-free placement module must
have exactly Lean's standard `[propext, Classical.choice, Quot.sound]`
footprint.
-/

open NSFormalization.Section3.T23

#print axioms DomainPlacementData
#print axioms domainPlacementCarrier
#print axioms domainPlacementCarrier_compact
#print axioms domainPlacementCarrier_bound
#print axioms domainPlacementRadius
#print axioms domainPlacementRadius_pos
#print axioms norm_le_domainPlacementRadius
#print axioms domainPlacementMargin
#print axioms domainPlacementMargin_pos
#print axioms domainPlacementThreshold
#print axioms domainPlacementThreshold_pos
#print axioms domainPlacementThreshold_le_one
#print axioms domainPlacementThreshold_time
#print axioms domainPlacementThreshold_space
#print axioms domainPlacementData
#print axioms domainPlacementData_time
#print axioms domainPlacementData_chartCenter
#print axioms domainPlacementData_chartRadius
#print axioms domainPlacementData_x₀
#print axioms interiorBall_in_domain
