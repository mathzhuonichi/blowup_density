import NSFormalization.Section4.A02.Energy

/-! Transitive-axiom audit for A02 unit U1a.  Run with
`cd verification && lake env lean ../research/A02/axioms_u1a.lean`.
Every line below must print exactly `propext, Classical.choice, Quot.sound`.

Lane 040 deduped the order-0 datum ⟹ `L²` step against `Section4.D01.DatumToJets`
(its general-order versions are what the registered contract
`verification/Bindings/DatumLemmas.lean` binds), so the former A02-local helpers
`memLp_of_isSobolevDatum`, `sliceLp_ae`, `l2Sq_le_of_isSobolevDatum` are gone; the
three deliverable theorems audited below now depend on the D01 lemmas. -/

#print axioms NSFormalization.Section4.A02.uniformFiniteEnergy_of_sobolev
#print axioms NSFormalization.Section4.A02.uniformFiniteEnergy_of_sobolevDatumPath
#print axioms NSFormalization.Section4.A02.ClassicalSolutionR.uniformFiniteEnergy
