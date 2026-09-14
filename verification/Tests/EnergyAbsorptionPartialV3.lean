import Contracts.V3.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartialV3
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one and version-two tests `Tests.EnergyAbsorptionPartial` /
`Tests.EnergyAbsorptionPartialV2` are untouched and keep running against
`Bindings.energyAbsorptionPartial` / `Bindings.energyAbsorptionPartialV2`; this is the third,
strongest acceptance test, not a replacement.  `Bindings.energyAbsorptionPartialV2_of_v3` is the
checked link: it projects `Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API`
out of the version-three witness by `rfl`, so nothing versions one and two guarantee is lost by
version three.

The two `example`s below print the new fields in the manuscript's shape (`eq:RL2`,
`04-whole-space.tex:116-121`; the differential bound is the doubled Cauchy–Schwarz form of
`02-preliminaries.tex:136-142`), each discharged by the corresponding field of the checked
witness, so a drift in a field type is a compile error here.

No `Formal.*` (HeliCorgi) module is imported here directly; the C01 proof closure is reached
only through `Bindings.EnergyAbsorptionPartialV3`, exactly as version two reaches it through
`Bindings.EnergyAbsorptionPartialV2` (so `warningAsError` is respected). -/

noncomputable section
namespace BlowupDensity.Tests

open Set MeasureTheory
open Contracts.V1.Data
open Contracts.V1.EnergyAbsorptionPartial (slice l2Sq l2Norm)
open Contracts.V2.EnergyAbsorptionPartial (gradientSq)
open Contracts.V3.EnergyAbsorptionPartial (forcePrimitive energyBudget)

/-- An implementation must supply every field of the unchanged version-one and version-two
specifications **and** the two ordinary-energy consequences of lane 154
(`Section4/C01/EnergyBounds.lean`): the Cauchy–Schwarz differential bound and eq:RL2.
`EnergyAbsorptionPartialV3API` carries the inherited data field `C₁`, so this is a `def`. -/
def checkedEnergyAbsorptionPartialV3 :
    Contracts.V3.EnergyAbsorptionPartial.EnergyAbsorptionPartialV3API :=
  Bindings.energyAbsorptionPartialV3

run_cmd TestSupport.checkAxioms ``checkedEnergyAbsorptionPartialV3

/-! ## The two new fields, in the manuscript's shape -/

section Shapes

/-- `energyDifferentialBound`, in the manuscript's shape (`04-whole-space.tex:116-121`, the
regularized-division input to eq:RL2; the doubled Cauchy–Schwarz form of
`02-preliminaries.tex:136-142`): `(‖u(t)‖₂²)' + 2ν‖∇u(t)‖₂² ≤ 2‖f(t)‖₂‖u(t)‖₂`. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ioo (0 : ℝ) T,
          ∀ E' : ℝ, HasDerivAt (fun s => l2Sq (slice w.velocity s)) E' t →
            E' + 2 * ν * gradientSq (slice w.velocity t) ≤
              2 * l2Norm (slice f t) * l2Norm (slice w.velocity t) :=
  checkedEnergyAbsorptionPartialV3.energyDifferentialBound

/-- `l2Bound` = **eq:RL2** (`04-whole-space.tex:116-121`, display at `:119`):
`‖u(t)‖₂ ≤ ‖a‖₂ + ∫₀ᵗ‖f(s)‖₂ ds =: K(t)`, with `K` spelled `energyBudget a f t`. -/
example :
    ∀ (ν : ℝ), 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
      ∀ f : SpaceTimeField, MemForceR f →
        ∀ (T : ℝ) (w : ClassicalSolutionR ν a f T), ∀ t ∈ Ico (0 : ℝ) T,
          l2Norm (slice w.velocity t) ≤ energyBudget a f t :=
  checkedEnergyAbsorptionPartialV3.l2Bound

end Shapes

end BlowupDensity.Tests
