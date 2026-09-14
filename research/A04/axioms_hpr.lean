import NSFormalization.Section4.A04.PressureDrop

open NSFormalization.Section4.A04

-- MAINT-flagged L²/ambient facts
#print axioms coordinates_inner_bilin
#print axioms complementSymbolComplex_inner_left
#print axioms lerayComplementL2_inner_left
#print axioms lerayComplementAmbient_inner_left
-- carrier bridge
#print axioms carrier_inner_eq
-- Step (S): self-adjointness + consequence
#print axioms lerayComplement_selfAdjoint
#print axioms inner_lerayComplement_eq_zero_of_eq_zero
-- Step (S–M): transverse velocity datum
#print axioms isSobolevDatum_zero
#print axioms velocity_datum_lerayComplement_eq_zero
-- Step (S): hpr
#print axioms pressure_drop
