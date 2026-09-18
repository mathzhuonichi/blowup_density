import NSFormalization.Section3.T15.Scaling

/-!
# T15 U-CAN axiom audit

The canonical statement layer introduces no mathematical axioms.  Every
declaration below has an axiom set contained in Lean's standard
`[propext, Classical.choice, Quot.sound]` footprint.
-/

open NSFormalization.Section3.T15

#print axioms IsLebesgueSlicePath
#print axioms mixedLebesgueENorm
#print axioms criticalOrder
#print axioms IsPeriodicLebesgueSlicePath
#print axioms mixedLebesgueENormT
#print axioms MemMixedLebesgueR
#print axioms MemMixedLebesgueT
#print axioms MemForceSobolevT
#print axioms EnergySlicesMemLpT
#print axioms PlacementData
#print axioms ScalingAPI
#print axioms scalingStatement
