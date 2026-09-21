import NSFormalization.Section4.D01.OrderZeroAlgebra
import NSFormalization.Section4.D01.MomentumSlice

open NSFormalization.Section4.D01

-- Group 1 (OrderZeroAlgebra)
#print axioms isSobolevDatum_sub
#print axioms orderZeroDatum_add
#print axioms orderZeroDatum_sub
#print axioms lerayComplement_orderZeroDatum_add
#print axioms lerayComplement_orderZeroDatum_sub

-- Group 2 (MomentumSlice)
#print axioms smoothL2_momentumResidual_slice
#print axioms memLp_pressureGradient_slice
#print axioms memLp_temporalDerivative_slice
#print axioms contDiff_temporalDerivative_slice
#print axioms sum_partialDeriv_temporalDerivative_eq_zero
#print axioms pressureGradient_apply
#print axioms partialDeriv_gradient_eq_sndFDeriv
#print axioms partialDeriv_pressureGradient_symm
