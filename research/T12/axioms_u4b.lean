import NSFormalization.Section3.T12.CriticalL3Density

/-!
# Axiom audit for lane 401 (T12 U4b)

Every public declaration of `Section3/T12/CriticalL3Density.lean` must print
exactly `[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T12

#print axioms NSFormalization.Section3.T12.torusLift_finitePeriodicFourierSum
#print axioms NSFormalization.Section3.T12.periodicFourierCoeff_finitePeriodicFourierSum
#print axioms NSFormalization.Section3.T12.periodicCharacter_neg
#print axioms NSFormalization.Section3.T12.conj_finitePeriodicFourierSum_real
#print axioms NSFormalization.Section3.T12.truncField
#print axioms NSFormalization.Section3.T12.truncField_apply
#print axioms NSFormalization.Section3.T12.ofReal_truncField_apply
#print axioms NSFormalization.Section3.T12.periodicFourierCoeff_truncField
#print axioms NSFormalization.Section3.T12.isPeriodicSpatial_truncField
#print axioms NSFormalization.Section3.T12.contDiff_truncField
#print axioms NSFormalization.Section3.T12.smoothPeriodicT_truncField
#print axioms NSFormalization.Section3.T12.freqBox
#print axioms NSFormalization.Section3.T12.mem_freqBox
#print axioms NSFormalization.Section3.T12.freqBox_neg_closed
#print axioms NSFormalization.Section3.T12.freqBox_mono
#print axioms NSFormalization.Section3.T12.exists_freqBox_superset
#print axioms NSFormalization.Section3.T12.tendsto_freqBox
#print axioms NSFormalization.Section3.T12.integrable_torusLift_truncField
#print axioms NSFormalization.Section3.T12.isMeanZeroT_truncField
#print axioms NSFormalization.Section3.T12.periodicHomogeneousENorm_truncField_le
#print axioms NSFormalization.Section3.T12.tendsto_eLpNorm_truncField_sub
#print axioms NSFormalization.Section3.T12.memPeriodicHomogeneous_of_smooth
#print axioms NSFormalization.Section3.T12.velocityCriticalL3
