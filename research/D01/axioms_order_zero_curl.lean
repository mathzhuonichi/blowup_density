import NSFormalization.Section4.D01.OrderZeroCurl

open NSFormalization.Section4.D01
open NSFormalization.Section4.D01.Cut
open NSFormalization.Section4.D01.Leray

-- Section 0/1/2 (Cut namespace)
#print axioms fderiv_zc_eq'
#print axioms cs_ibp
#print axioms cs_weighted_pairing_zero
#print axioms physical_weighted_pairing_zero
#print axioms wAnti
#print axioms sum_wAntisym_mul
#print axioms physical_antisym_pairing_zero

-- Section 3/4 (D01 namespace)
#print axioms fourier_lineDeriv_apply
#print axioms tempered_antisym_eq
#print axioms fourier_antisym
#print axioms orderZeroDatum_longitudinal_symm
#print axioms longitudinal_of_longitudinal_symm
#print axioms orderZeroDatum_longitudinal_of_curl_free

-- Corollary (Leray namespace)
#print axioms lerayComplement_zero_orderZeroDatum_eq_self
