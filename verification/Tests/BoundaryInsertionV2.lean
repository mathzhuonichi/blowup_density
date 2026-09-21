import Contracts.V2.BoundaryInsertion
import Bindings.BoundaryInsertionV2
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedBoundaryInsertionV2 :
    Contracts.V2.BoundaryInsertion.boundaryInsertionStatementV2 :=
  Bindings.BoundaryInsertion.boundaryInsertionStatementV2_holds

run_cmd TestSupport.checkAxioms ``checkedBoundaryInsertionV2
run_cmd TestSupport.checkAxioms ``NSFormalization.Section3.T23.ibp_of_isOpen_isBounded

/-- The accepted conclusion is the previously unregistered strong statement,
not the conditional V1 conjunction. No `IBP` argument is supplied by the caller. -/
example : Contracts.V1.BoundaryInsertion.boundaryInsertionStatement' :=
  checkedBoundaryInsertionV2

end BlowupDensity.Tests
