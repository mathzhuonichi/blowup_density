import NSFormalization.Section3.T11.RestartBeyond

/-! Transitive-axiom audit for T11/U13 (`RestartBeyond.lean`).

Every declaration of the module prints exactly the three standard axioms. -/

open NSFormalization.Section3.T11

/-- info: 'NSFormalization.Section3.T11.velocity_hasDerivAt_timeT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms velocity_hasDerivAt_timeT

/-- info: 'NSFormalization.Section3.T11.velocitySlice_mem_initialClassT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms velocitySlice_mem_initialClassT

/-- info: 'NSFormalization.Section3.T11.restrictClassicalSolutionT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restrictClassicalSolutionT

/-- info: 'NSFormalization.Section3.T11.restrictClassicalSolutionT_velocity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms restrictClassicalSolutionT_velocity

/-- info: 'NSFormalization.Section3.T11.restrictClassicalSolutionT_pressure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms restrictClassicalSolutionT_pressure

/-- info: 'NSFormalization.Section3.T11.solvesBelowT_of_classicalSolutionT' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms solvesBelowT_of_classicalSolutionT

/-- info: 'NSFormalization.Section3.T11.shiftedSolutionT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shiftedSolutionT

/-- info: 'NSFormalization.Section3.T11.restartedResidualT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restartedResidualT

/-- info: 'NSFormalization.Section3.T11.shifted_velocity_uniqueT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shifted_velocity_uniqueT

/-- info: 'NSFormalization.Section3.T11.shifted_pressure_uniqueT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms shifted_pressure_uniqueT

/-- info: 'NSFormalization.Section3.T11.glueClassicalSolutionT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms glueClassicalSolutionT

/-- info: 'NSFormalization.Section3.T11.restartBeyond' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restartBeyond
