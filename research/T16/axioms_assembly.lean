import NSFormalization.Section3.T16.Assembly

/-! Axiom audit for the T16 assembly module.  Every declaration must print
`[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section3.T16

#print axioms contDiff_cutoffSmul_of_ballSmooth
#print axioms spatialCutoff_tsupport_ball
#print axioms temporalCutoff_tsupport_Ioo
#print axioms cutoffPotential_contDiff
#print axioms physicalCorrection_contDiff
#print axioms physicalCorrection_divergence
#print axioms latticeLift_sliceSupport_closed
#print axioms periodicSet_mono
#print axioms plateau_subset_ball
#print axioms physicalCorrection_cancels
#print axioms localPotentialData
#print axioms localPotentialAPI
#print axioms localPotential
