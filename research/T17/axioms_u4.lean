import NSFormalization.Section3.T17.ForceProfile

/-! Axiom audit for T17 U4 (`Section3/T17/ForceProfile.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section3.T17

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
