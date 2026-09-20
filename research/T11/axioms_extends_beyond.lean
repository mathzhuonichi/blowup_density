import NSFormalization.Section3.T11.ExtendsBeyond

/-! Transitive-axiom audit for T11/U14 + U16 (`ExtendsBeyond.lean`).

Every declaration of the module prints exactly the three standard axioms. -/

open NSFormalization.Section3.T11

/-- info: 'NSFormalization.Section3.T11.lifespan_ge_of_horizon' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lifespan_ge_of_horizon

/-- info: 'NSFormalization.Section3.T11.lifespan_ge_of_extends' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms lifespan_ge_of_extends

/-- info: 'NSFormalization.Section3.T11.extendsBeyond_of_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms extendsBeyond_of_input

/-- info: 'NSFormalization.Section3.T11.periodicMaximalExistenceInput_of_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms periodicMaximalExistenceInput_of_input

/-- info: 'NSFormalization.Section3.T11.exists_maximal_of_input' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_maximal_of_input

/-- info: 'NSFormalization.Section3.T11.lifespanInfiniteOfLocallyFinite_of_input' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms lifespanInfiniteOfLocallyFinite_of_input

/-- info: 'NSFormalization.Section3.T11.squaredHTwoIntegralT_ne_top_of_lt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms squaredHTwoIntegralT_ne_top_of_lt

/-- info: 'NSFormalization.Section3.T11.constantVelocitySolutionT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms constantVelocitySolutionT

/-- info: 'NSFormalization.Section3.T11.squaredHTwoIntegralT_constant_ne_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms squaredHTwoIntegralT_constant_ne_top
