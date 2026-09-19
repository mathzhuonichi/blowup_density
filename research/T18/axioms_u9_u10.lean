import NSFormalization.Section3.T18.EnergyRate
import NSFormalization.Section3.T18.MixedRate

/-!
# T18 U9/U10 axiom audit

Every public declaration introduced by the two canonical modules must print
exactly Lean's standard `[propext, Classical.choice, Quot.sound]` footprint.
-/

open NSFormalization.Section3.T18

#print axioms energyTorusChart
#print axioms contDiffOn_spatialFDeriv
#print axioms spatialGradient_add
#print axioms gradientSliceNorm_aemeasurable
#print axioms energyEssSupT_add_le
#print axioms energyGradientT_add_le
#print axioms energyENormT_add_le
#print axioms velocityDifference_eq_correction_add_packet
#print axioms velocityDifference_energyENorm_le
#print axioms packet_energyENorm_eq
#print axioms energyRate_separateConstants

#print axioms mixedLebesgueENormT_eq_of_path
#print axioms mixedLebesgueENorm_eq_of_path
#print axioms memMixedLebesgueT_of_lt_top
#print axioms periodicLebesgueSlicePath_add
#print axioms memMixedLebesgueT_add
#print axioms mixedLebesgueENormT_add_le
#print axioms correctionForce_mixed_memLp
#print axioms packetSource_mixedNorm_ne_top
#print axioms forceDiffMixedConst
#print axioms forceDiffMixedConst_nonneg
#print axioms forceDifference_mixed_memLp
#print axioms forceDifference_mixed_bound
