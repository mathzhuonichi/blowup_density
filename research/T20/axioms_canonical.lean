import NSFormalization.Section3.T20.CriticalRegularity

/-!
# T20 canonical transitive-axiom audit

Every declaration introduced by the canonical statement module and its probe
conversions is expected to print exactly `[propext, Classical.choice,
Quot.sound]`.  The `Nonempty` statement is audited only as a definition; no
API witness is constructed in this statement lane.
-/

#print axioms NSFormalization.Section3.T20.meanPathT
#print axioms NSFormalization.Section3.T20.meanFreeVelocity
#print axioms NSFormalization.Section3.T20.meanFreeForce
#print axioms NSFormalization.Section3.T20.constantTransportT
#print axioms NSFormalization.Section3.T20.constantTransportSpatialT
#print axioms NSFormalization.Section3.T20.meanForceIntegralT
#print axioms NSFormalization.Section3.T20.criticalY
#print axioms NSFormalization.Section3.T20.criticalZ
#print axioms NSFormalization.Section3.T20.criticalB
#print axioms NSFormalization.Section3.T20.criticalBIntegral
#print axioms NSFormalization.Section3.T20.criticalRho
#print axioms NSFormalization.Section3.T20.gradientSqT
#print axioms NSFormalization.Section3.T20.laplacianSqT
#print axioms NSFormalization.Section3.T20.lTwoSqT
#print axioms NSFormalization.Section3.T20.meanFreeForceLTwoSqIntegral
#print axioms NSFormalization.Section3.T20.meanModeCriterionIntegral
#print axioms NSFormalization.Section3.T20.periodicPairing
#print axioms NSFormalization.Section3.T20.CriticalRegularityTAPI
#print axioms NSFormalization.Section3.T20.criticalRegularityStatement
