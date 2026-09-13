import NSFormalization.Section4.D01.LerayDatum

open NSFormalization.Section4.D01.Leray

-- Item 2 (reality)
#print axioms realSymmetryVec_assemble
#print axioms image_component_mem_realSubspace
-- Item 1 (ambient multiplier)
#print axioms lerayComplementL2_norm_le
#print axioms lerayComplementAmbient
#print axioms lerayComplementAmbient_apply
#print axioms lerayComplementAmbient_opNorm_le_one
-- Item 3 (datum-carrier multiplier)
#print axioms lerayComplement
#print axioms lerayComplement_coe
#print axioms lerayComplement_toAmbient
-- Item 4 (properties)
#print axioms lerayComplement_opNorm_le_one
#print axioms lerayComplement_idempotent
#print axioms lerayComplement_ae
#print axioms inner_r3FreqVec
#print axioms lerayComplement_eq_zero_of_transverse
