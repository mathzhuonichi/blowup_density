import NSFormalization.Section3.T11.FlowConversion

/-!
# Transitive-axiom audit for T11 U1

The permitted transitive axiom set is
`[propext, Classical.choice, Quot.sound]`; no declaration below may introduce
an axiom outside that set.
-/

open NSFormalization.Section3.T11

#print axioms source_residual_eq_navierStokesResidual
#print axioms isPeriodicOn_iff_unitSpatialPeriodsOn
#print axioms toFlow
#print axioms ofFlow
#print axioms toFlow_velocity
#print axioms toFlow_pressure
#print axioms ofFlow_velocity
#print axioms ofFlow_pressure
#print axioms toFlow_ofFlow
#print axioms ofFlow_toFlow
#print axioms memForceT_to_isSmoothPeriodicForce
