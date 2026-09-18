import NSFormalization.Section3.T17.CorrectionProfile

/-! Axiom audit for T17 U3 (`Section3/T17/CorrectionProfile.lean`).
Every declaration must print exactly `[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section3.T17

#print axioms rescaledCorrectionProfile_eq_profile
#print axioms profile_eq_curl_slice
#print axioms contDiff_rescaledCorrectionProfile
#print axioms norm_iteratedFDeriv_slice_le
#print axioms correction_profile_smooth
#print axioms correction_profile_support
#print axioms correctionProfileConst
#print axioms correctionProfileConst_nonneg
#print axioms correction_profile_uniform
#print axioms correction_eq_physicalCorrection
#print axioms correction_profile_identity
