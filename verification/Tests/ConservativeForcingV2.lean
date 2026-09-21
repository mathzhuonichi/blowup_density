import Contracts.V2.ConservativeForcing
import Bindings.ConservativeForcingV2
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedConservativeForcingV2 :
    Contracts.V2.ConservativeForcing.conservativeForcingStatementV2 :=
  Bindings.ConservativeForcingV2.conservativeForcingStatementV2_holds

run_cmd TestSupport.checkAxioms ``checkedConservativeForcingV2
run_cmd TestSupport.checkAxioms ``NSFormalization.Section3.T24.restSolutionOmega
run_cmd TestSupport.checkAxioms ``NSFormalization.Section3.T24.potential_pairingOmega
run_cmd TestSupport.checkAxioms ``NSFormalization.Section3.T24.zero_from_restOmega

/-- The old torus statement remains a projection of V2. -/
example : Contracts.V1.ConservativeForcingAPI := checkedConservativeForcingV2.1

/-- The domain statement is a separate projection using registered domain types. -/
example : Contracts.V2.ConservativeForcing.ConservativeForcingOmegaAPI :=
  checkedConservativeForcingV2.2

end BlowupDensity.Tests
