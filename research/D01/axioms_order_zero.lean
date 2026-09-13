import NSFormalization.Section4.D01.OrderZeroSymbol
/-!
Axiom audit for the SL7b-α order-0 transverse module (lane 094).
Every public declaration must depend only on `propext, Classical.choice, Quot.sound`.
-/
open NSFormalization.Section4.D01

-- Cut namespace (cutoff infrastructure + analytic heart)
#print axioms Cut.norm_cv
#print axioms Cut.chi_smooth
#print axioms Cut.chi_cs
#print axioms Cut.chi_eventually_one
#print axioms Cut.exists_deriv_bound
#print axioms Cut.chi_deriv_bound
#print axioms Cut.zc_eq
#print axioms Cut.hasFDeriv_zc
#print axioms Cut.zc_smooth
#print axioms Cut.fderiv_zc_eq
#print axioms Cut.sum_fderiv_zc
#print axioms Cut.cs_pairing_zero
#print axioms Cut.physical_pairing_zero

-- D01 reduction + Lemma A
#print axioms tempered_div_zero
#print axioms fourier_transverse
#print axioms angularWeightSymbol_zero
#print axioms orderZeroDatum_coe
#print axioms orderZeroDatum_symm_ae
#print axioms orderZeroDatum_transverse_symm
#print axioms transverse_of_transverse_symm
#print axioms orderZeroDatum_transverse_of_divergence_free
