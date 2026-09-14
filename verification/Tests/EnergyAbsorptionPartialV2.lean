import Contracts.V2.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartialV2
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one test `Tests.EnergyAbsorptionPartial` is untouched and keeps running against
`Bindings.energyAbsorptionPartial`; this is the second, stronger acceptance test, not a
replacement.  `Bindings.energyAbsorptionPartial_of_v2` is the checked link between the two:
it records that the version-two witness projects, by `rfl`, onto the frozen version-one
witness, so nothing that version one guarantees is lost by version two.

No `Formal.*` (HeliCorgi) module is imported here directly; the C01 proof closure is reached
only through `Bindings.EnergyAbsorptionPartialV2`, exactly as version one reaches it through
`Bindings.EnergyAbsorptionPartial` (so `warningAsError` is respected). -/

noncomputable section
namespace BlowupDensity.Tests

open Set MeasureTheory
open Contracts.V1.Data
open Contracts.V1.EnergyAbsorptionPartial (slice l2Sq)
open Contracts.V2.EnergyAbsorptionPartial (gradientSq pairing)

/-- An implementation must supply every field of the unchanged version-one specification
**and** the ordinary energy identity `energyIdentity` of lanes 143 and 150.
`EnergyAbsorptionPartialV2API` carries the inherited data field `C₁`, so this is a `def`. -/
def checkedEnergyAbsorptionPartialV2 :
    Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API :=
  Bindings.energyAbsorptionPartialV2

run_cmd TestSupport.checkAxioms ``checkedEnergyAbsorptionPartialV2

/-- `energyIdentity`, in the manuscript's shape (`04-whole-space.tex:117`, display at
`02-preliminaries.tex:136-139`): `(‖u(t)‖₂²)' = −2ν‖∇u(t)‖₂² + 2⟨u(t), f(t)⟩`. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivAt (fun s => l2Sq (slice w.velocity s))
            (-2 * ν * gradientSq (slice w.velocity t) +
              2 * pairing (slice w.velocity t) (slice f t)) t :=
  checkedEnergyAbsorptionPartialV2.energyIdentity

end BlowupDensity.Tests
