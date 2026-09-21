import Tests.TorusLocalTheoryV2
import TestSupport.Axioms

#print axioms NSFormalization.Section3.T11.restartBeyondH1T
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section3.T11.restartBeyondH1T
  let actual ← Lean.collectAxioms ``NSFormalization.Section3.T11.restartBeyondH1T
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms BlowupDensity.Bindings.torusContinuationH1API
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.torusContinuationH1API
  let actual ← Lean.collectAxioms ``BlowupDensity.Bindings.torusContinuationH1API
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms BlowupDensity.Bindings.torusLocalTheoryV2_holds
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.torusLocalTheoryV2_holds
  let actual ← Lean.collectAxioms ``BlowupDensity.Bindings.torusLocalTheoryV2_holds
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"

#print axioms BlowupDensity.Tests.checkedTorusLocalTheoryV2
run_cmd do
  BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Tests.checkedTorusLocalTheoryV2
  let actual ← Lean.collectAxioms ``BlowupDensity.Tests.checkedTorusLocalTheoryV2
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.size == 3 && expected.all actual.contains do
    throwError "Expected exactly the three standard axioms"
