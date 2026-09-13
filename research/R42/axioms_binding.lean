import Bindings.InsertionLifespan

/-! Axiom audit for lane 092 (R42 lifespan Bindings assembly).  Every public
declaration of `Bindings/InsertionLifespan.lean` must print exactly
`[propext, Classical.choice, Quot.sound]`. -/

open BlowupDensity.Bindings.InsertionLifespan

#print axioms sol_on_shorter
#print axioms memForceR_force
#print axioms initialClassR_a
#print axioms lifespan_lower
#print axioms lifespan_upper
#print axioms lifespan_eq
#print axioms referenceLifespan
#print axioms insertionLifespan
#print axioms insertionLifespan_family

/-! Lane 098 additions (R42 full horizon): the two new Bindings declarations
`sol_fullHorizon` and `isMaximalSolution_of_inserted` must also print exactly
`[propext, Classical.choice, Quot.sound]`. -/

#print axioms sol_fullHorizon
#print axioms isMaximalSolution_of_inserted
