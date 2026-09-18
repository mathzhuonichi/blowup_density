import NSFormalization.Section3.T17.Correction

/-!
# T17 U-CAN axiom audit

The canonical statement layer and the canonical U4 vocabulary introduced on
this lane use no mathematical axioms.  Every declaration below must remain in
Lean's standard `[propext, Classical.choice, Quot.sound]` footprint.
-/

open NSFormalization.Section3.T17

#print axioms rescaledReference
#print axioms rescaledForceProfile
#print axioms spatialDerivative_rescaledReference
#print axioms rescaledReference_spatialDerivative_smul
#print axioms rescaledForceProfile_eq_forceProfile
#print axioms force_profile_smooth
#print axioms force_profile_support
#print axioms forceProfileConst
#print axioms forceProfileConst_nonneg
#print axioms force_profile_uniform
#print axioms inverseScale_correctionChartPoint
#print axioms physicalForce_eq_rescaledForceProfile
#print axioms torusSpaceTimeLift
#print axioms torusSpatialSupport
#print axioms torusTemporalSupport
#print axioms CorrectionAPI
#print axioms correctionStatement
