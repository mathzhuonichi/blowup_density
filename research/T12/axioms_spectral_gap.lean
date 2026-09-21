import NSFormalization.Section3.T12.SpectralGap

/-!
# Transitive-constant audit for the periodic spectral-gap module

Every exported declaration below must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T12

#print axioms gapConst
#print axioms gapConst_pos
#print axioms homogeneousDatumWeight_le_periodicFrequencyWeight_rpow
#print axioms periodicFrequencyWeight_rpow_le_gap_mul_homogeneous
#print axioms reweightDatum
#print axioms reweightDatum_apply
#print axioms reweightDatum_norm_le
#print axioms reweightDatum_real
#print axioms homogeneous_le_sobolev
#print axioms spectralGap
