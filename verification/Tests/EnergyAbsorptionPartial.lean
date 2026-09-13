import Contracts.V1.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartial
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked. -/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged specification. -/
def checkedEnergyAbsorptionPartial :
    Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI :=
  Bindings.energyAbsorptionPartial

run_cmd TestSupport.checkAxioms ``checkedEnergyAbsorptionPartial

end BlowupDensity.Tests
