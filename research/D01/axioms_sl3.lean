import NSFormalization.Section4.D01.LerayMultiplier

/-! Axiom conformance for lane 073 (D01 · P2 · SL3/SL2), the operator-valued L²
Leray-complement multiplier.  Every declaration below should report only the standard
logical axioms `[propext, Classical.choice, Quot.sound]`. -/

open NSFormalization.Section4.D01.Leray

-- The complex fibre symbol
#print axioms complementSymbolComplex
#print axioms complementSymbolComplex_apply
#print axioms complementSymbolComplex_opNorm_le_one
#print axioms complementSymbolComplex_idempotent
#print axioms r3LeraySymbolComplex_add_complementSymbolComplex
#print axioms complementSymbolComplex_eq_zero_of_inner_eq_zero

-- The bundled operator-valued L² multiplier (SL3)
#print axioms lerayComplementL2
#print axioms lerayComplementL2_opNorm_le_one
#print axioms lerayComplementL2_ae
#print axioms lerayComplementL2_idempotent

-- The complementary solenoidal projector / Helmholtz decomposition
#print axioms lerayL2
#print axioms lerayL2_add_lerayComplementL2
#print axioms lerayL2_ae

-- Fibre facts lifted to L² fields
#print axioms lerayComplementL2_eq_self_of_longitudinal
#print axioms lerayComplementL2_eq_zero_of_transverse

-- Reality preservation (SL2)
#print axioms conjR3C_complementSymbolComplex
#print axioms realSymmetryVec_lerayComplementL2
#print axioms realSymmetryVec_lerayComplementL2_eq_self

-- The q=2 assemble/coordinates isometry (datum-carrier bridge, reviewer's work item)
#print axioms coordinates_ae
#print axioms coordinates_inner_self
#print axioms coordinates_norm

-- Datum-carrier bridge completed (after the reviewer's probes, REVIEW_SL3.md)
#print axioms coordinates_assemble
#print axioms assemble_norm
#print axioms coordinates_realSymmetryVec
