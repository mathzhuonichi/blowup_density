import Contracts.V2.PeriodicInsertion
import Bindings.PeriodicInsertionV2
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedPeriodicInsertionV2 :
    Contracts.V2.PeriodicInsertion.periodicInsertionStatementV2 :=
  Bindings.PeriodicInsertion.periodicInsertionStatementV2_holds

run_cmd TestSupport.checkAxioms ``checkedPeriodicInsertionV2
run_cmd TestSupport.checkAxioms ``NSFormalization.Section3.T19.periodicInsertion_from_data
run_cmd TestSupport.checkAxioms ``NSFormalization.Section3.T19.At.velocityDifference_support

end BlowupDensity.Tests
