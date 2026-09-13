import NSFormalization.Section4.D01.LerayLowering

open NSFormalization.Section4.D01.Leray

/-! Axiom audit for D01 · P2 · SL7c (`Section4/D01/LerayLowering.lean`).
Every public declaration must depend only on `propext`, `Classical.choice`, `Quot.sound`.
(`angularFrequencyDilation_coeFn` now lives in lane 079's merged `Section4/D01/Transverse.lean`
and is imported, not re-proved here.) -/

#print axioms assemble_vec_ae
#print axioms loweringMult
#print axioms angularOrderLowering_coeFn
#print axioms loweringMult_eq
#print axioms angularOrderLowering_coeFn'
#print axioms angularOrderLowering_self_of_coeFn
#print axioms lerayComplement_lowerVectorL
#print axioms isSobolevDatum_lower
#print axioms isSobolevDatum_lower_iff
#print axioms leray_datum_lower
