import NSFormalization.Section4.D01.FiniteOrderDatum

open NSFormalization.Section4.D01

-- Row D-c: the pointwise symbol bound and its norm form.
#print axioms sqrt_one_add_normSq_le
#print axioms norm_sobolevBesselWeight_one
#print axioms norm_raiseIntegrand_le
#print axioms continuous_sobolevBesselWeight_one
-- Row D-d2 reduction: the L² assembly of the raising witness.
#print axioms raisableWitness_of_memLp_smul
-- Row D-d1: the order-raising step (the induction step).
#print axioms raise_mem
#print axioms angularRealization_raiseHilbert
#print axioms isSobolevDatum_raise
-- The three def/rfl exports (lane-125 review, finding 1): in the closure of the theorems above,
-- listed for completeness so every later D01 lane's sweep covers all 11 exports.
#print axioms RaisableWitness
#print axioms raiseHilbert
#print axioms coe_raiseHilbert
