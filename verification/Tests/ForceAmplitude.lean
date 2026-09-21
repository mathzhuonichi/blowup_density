import Contracts.V1.ForceAmplitude
import Bindings.ForceAmplitude
import TestSupport.Axioms

namespace BlowupDensity.Tests

theorem checkedForceAmplitude : Contracts.V1.forceAmplitudeStatement :=
  Bindings.forceAmplitude

run_cmd TestSupport.checkAxioms ``checkedForceAmplitude
run_cmd TestSupport.checkAxioms ``Bindings.forceAmplitude_from_data
run_cmd TestSupport.checkAxioms ``Bindings.selectedPacketForce_ne_zero

end BlowupDensity.Tests
