import Contracts.V3.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartialV3
import Tests.EnergyAbsorptionPartialV3

/-!
# Conformance: the two ordinary-energy consequences as the version-3 C01 contract

Checks that the checked witness `BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3`
(= `Bindings.energyAbsorptionPartialV3`, inhabiting
`Contracts.V3.EnergyAbsorptionPartial.EnergyAbsorptionPartialV3API`) depends on only the
standard logical axioms, that the version-2 projection is the frozen version-2 witness (`rfl`),
that the two new spec-local `def`s `forcePrimitive`/`energyBudget` are the tree's
(`rfl`), and that the two lane-154 theorems the new fields are bound to still use only the
standard axioms.

Run: `cd verification && lake env lean ../research/C01/axioms_v3_contract.lean`
Expected: every `#print axioms` prints exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace BlowupDensity.Bindings

/-! ## `rfl` bridges: the two new spec-local defs are the tree's own -/

example : Contracts.V3.EnergyAbsorptionPartial.forcePrimitive
    = NSFormalization.Section4.C01.forcePrimitive := rfl
example : Contracts.V3.EnergyAbsorptionPartial.energyBudget
    = NSFormalization.Section4.C01.energyBudget := rfl

/-! ## The version-2 projection is the frozen version-2 witness -/

example : energyAbsorptionPartialV3.toEnergyAbsorptionPartialV2API = energyAbsorptionPartialV2 :=
  rfl

end BlowupDensity.Bindings

/-! ## The checked witness and the two lane-154 theorems it is bound to -/

#print axioms BlowupDensity.Tests.checkedEnergyAbsorptionPartialV3
#print axioms NSFormalization.Section4.C01.energyDifferentialBound
#print axioms NSFormalization.Section4.C01.l2Bound
