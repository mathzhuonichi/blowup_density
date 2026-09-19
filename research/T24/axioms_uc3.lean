import Bindings.ConservativeForcing
import Tests.ConservativeForcing

/-! Transitive-axiom audit for T24c unit Uc3.

Every proof/witness assembled or transported by this unit must print exactly
`[propext, Classical.choice, Quot.sound]`.
-/

open NSFormalization.Section3.T24

/-- info: 'NSFormalization.Section3.T24.conservativeForcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conservativeForcing

/-- info: 'NSFormalization.Section3.T24.restSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms restSolution

/-- info: 'BlowupDensity.Bindings.ConservativeForcing.conservativeForcing' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BlowupDensity.Bindings.ConservativeForcing.conservativeForcing

/-- info: 'BlowupDensity.Bindings.ConservativeForcing.conservativeForcingStatement_holds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms BlowupDensity.Bindings.ConservativeForcing.conservativeForcingStatement_holds

/-- info: 'BlowupDensity.Bindings.ConservativeForcing.restSolution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlowupDensity.Bindings.ConservativeForcing.restSolution

/-- info: 'BlowupDensity.Tests.checkedConservativeForcing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BlowupDensity.Tests.checkedConservativeForcing

/-! Repeat the guarded audit as visible gate output for the lane report. -/

#print axioms conservativeForcing
#print axioms restSolution
#print axioms BlowupDensity.Bindings.ConservativeForcing.conservativeForcing
#print axioms BlowupDensity.Bindings.ConservativeForcing.conservativeForcingStatement_holds
#print axioms BlowupDensity.Bindings.ConservativeForcing.restSolution
#print axioms BlowupDensity.Tests.checkedConservativeForcing
