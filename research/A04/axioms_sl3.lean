import NSFormalization.Section4.D01.DerivativeDatum
import NSFormalization.Section4.A04.LaplacianDatum

/-!
Conformance / axiom audit for A04 unit G1, sub-lemma SL3 (the dissipation identity on the
datum carrier) and the shared D01/P2 derivative-datum step.  Every public declaration of the
two new modules is audited.  Expected: only the standard logical axioms `propext`,
`Classical.choice`, `Quot.sound`.
Run: `cd verification && lake env lean ../research/A04/axioms_sl3.lean`.
-/

open NSFormalization.Paper3
open NSFormalization.Section4.D01
open NSFormalization.Section4.A04

-- D01/P2 · A04/SL3 shared: the angular directional-derivative multiplier
#print axioms angularDirectionalDerivative
#print axioms angularRealization_directionalDerivative
#print axioms conj_sobolevDirectionalSymbol_neg
#print axioms realSymmetry_sobolevDirectionalDerivative
#print axioms cyclesToAngular_symm_realSymmetry
#print axioms realSymmetry_angularDirectionalDerivative
#print axioms angularDirectionalDerivative_mem_realSubspace
#print axioms angularDirectionalDerivativeReal
#print axioms angularDirectionalDerivativeReal_coe

-- symbol facts for the SL3 pairing identity
#print axioms cycles_symbol_imaginary
#print axioms angularWeightSymbol_conj
#print axioms lowering_symbol_real
#print axioms mid_symbol_imaginary
#print axioms weight_product_order_indep
#print axioms mid_symbol_order_independent

-- the derivative datum itself
#print axioms angularRealization_of_isSobolevDatum
#print axioms isSobolevDatum_partialDeriv

-- A04/SL3: the dissipation norm and the gradient identification
#print axioms gradientSobolevNormAt
#print axioms gradientSobolevENorm_toReal_sq_eq_sum
#print axioms gradientSobolevNormAt_sq_eq_sum
#print axioms gradientSobolevENorm_toReal_sq_eq_datum_sum
