import Contracts.V2.Correction3
import Bindings.Correction3V2
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedCorrection3V2 : Contracts.V2.Correction3.correctionStatementV2 :=
  Bindings.Correction3.correctionStatementV2_holds

run_cmd TestSupport.checkAxioms ``checkedCorrection3V2

run_cmd TestSupport.checkAxioms ``Bindings.Correction3.correctionArticle_of_packet

end BlowupDensity.Tests
