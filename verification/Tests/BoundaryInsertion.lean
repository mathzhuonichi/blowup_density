import Contracts.V1.BoundaryInsertion
import Bindings.BoundaryInsertion
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedBoundaryInsertion : Contracts.V1.BoundaryInsertion.boundaryInsertionStatementV1 :=
  Bindings.BoundaryInsertion.Contract.boundaryInsertionStatementV1_holds

run_cmd TestSupport.checkAxioms ``checkedBoundaryInsertion

example : Contracts.V1.BoundaryInsertion.boundaryInsertionStatement'_box :=
  checkedBoundaryInsertion.1

example : Contracts.V1.BoundaryInsertion.boundaryInsertionStatement'_of_ibp :=
  checkedBoundaryInsertion.2

end BlowupDensity.Tests
