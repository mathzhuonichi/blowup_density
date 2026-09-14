-- Axiom audit for lane 132 (D01 · C1b-m-D close): row D-b-transport + D-close.
-- Every new declaration of `Section4/D01/FiniteOrderConstructor.lean` must print
-- exactly [propext, Classical.choice, Quot.sound].  Compiles under `lake env lean` from verification/.
import NSFormalization.Section4.D01.FiniteOrderConstructor

open NSFormalization.Section4.D01

-- §0 promoted probes
#print axioms isSobolevDatum_partialDeriv_weak
#print axioms db_cycles_full
-- §1 the transport (row D-b-transport, the new work)
#print axioms coord_smul_deriv_ae
#print axioms memLp_coord_smul_datum
-- §2 the finite-order constructor (row D-close)
#print axioms HasWeakDerivsL2
#print axioms weakDerivs_mono
#print axioms exists_isSobolevDatum_of_memLp_derivs
-- §3 non-vacuity
#print axioms smoothField_weakDeriv_pairing
#print axioms weakDerivs_smooth
