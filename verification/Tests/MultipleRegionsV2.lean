import Contracts.V2.MultipleRegions
import Bindings.MultipleRegionsV2
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedMultipleRegionsV2 :
    Contracts.V2.MultipleRegions.multipleRegionsStatementV2 :=
  Bindings.MultipleRegionsV2.multipleRegionsStatementV2_holds

run_cmd TestSupport.checkAxioms ``checkedMultipleRegionsV2

example : Contracts.V1.multipleRegionsStatement := checkedMultipleRegionsV2.1
example : Contracts.V2.MultipleRegions.multipleRegionsOmegaStatement := checkedMultipleRegionsV2.2

end BlowupDensity.Tests
