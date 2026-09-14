import Contracts.V2.EnergyHighPartial
import Bindings.EnergyHighPartial
import NSFormalization.Section4.A04.Forcing
import NSFormalization.Section4.A04.HighContinuation
import NSFormalization.Section4.A04.HighContinuationIntegral

/-! The implementation layer for the version-two energy-high-partial contract, and
the compatibility bridge back to version one.

`Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API` extends
`Contracts.V1.EnergyHighPartial.EnergyHighPartialAPI` by the constant `Cgron` and the
two `ζ`-continuation fields `regularizedNormDerivative`
(`NSFormalization.Section4.A04.regularizedNormDerivative`, lane 135, unit **G2**) and
`highContinuationIntegral`
(`NSFormalization.Section4.A04.highContinuationIntegral`, lane 138, unit **G2b**), so
this file has these jobs.

* `energyHighPartialV2` inhabits the version-two record.  It reuses the frozen
  version-one witness `Bindings.energyHighPartial` with `{ … with … }`, binds
  `Cgron`/`Cgron_pos` to `A04.Cgron`/`A04.Cgron_pos`, and fills the two continuation
  fields with the `Section4/A04` theorems, transported across the two
  `ClassicalSolutionR` copies by the reused `Bindings.uniqueness_toA02` exactly as
  version one's `energyIdentityHigh` does — `(uniqueness_toA02 w).velocity = w.velocity`
  by `rfl` and `w.velocity` is the only projection the statements mention.
* `energyHighPartialV2_memL1Hm_eq` records by `rfl` that the contract's `MemL1Hm`
  (`Contracts/V2/EnergyHighPartial.lean`) is the implementation's
  `NSFormalization.Section4.A04.MemL1Hm` — the **fourth** `rfl` bridge of this
  contract family (`Section4/A04/Forcing.lean`'s `forceSobolevENormL1` is
  field-for-field defeq to `Contracts.V1.Data`'s, the module docstring of
  `Forcing.lean` records this).
* `energyHighPartialV2_Cgron_eq` records the opaque `Cgron`'s value
  `(Chigh m)²/(4ν)` at the binding level only (`A04.Cgron`'s definition), the analogue
  of version one's `energyHighPartial_Chigh_eq_Ctame`.
* `energyHighPartial_of_v2` records by `rfl` that the inherited version-one projection
  is the frozen version-one witness `Bindings.energyHighPartial`.

Every declaration carries an `energyHighPartial`/`energyHighPartialV2` prefix;
`BlowupDensity.Bindings` is a flat namespace shared by all adapters. -/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

/-- **The fourth `rfl` bridge.**  The contract's restated `MemL1Hm`
(`Contracts/V2/EnergyHighPartial.lean`) is the implementation's
`NSFormalization.Section4.A04.MemL1Hm` (`Section4/A04/Forcing.lean:110`).  Both are
`∀ m, forceSobolevENormL1 (m:ℝ) f ≠ ⊤`, and `Section4/A04/Forcing.lean`'s
`forceSobolevENormL1` is field-for-field definitionally equal to `Contracts.V1.Data`'s
(`Forcing.lean:104-106`, the docstring's "field-for-field definitionally equal"). -/
theorem energyHighPartialV2_memL1Hm_eq :
    Contracts.V2.EnergyHighPartial.MemL1Hm
      = NSFormalization.Section4.A04.MemL1Hm := rfl

/-- Bind the version-two contract: version one's frozen witness plus the continuation
constant and the two `ζ`-continuation fields.  The record carries data fields, so this
is a `def`, as in version one. -/
def energyHighPartialV2 :
    Contracts.V2.EnergyHighPartial.EnergyHighPartialV2API :=
  { energyHighPartial with
    Cgron := NSFormalization.Section4.A04.Cgron
    Cgron_pos := NSFormalization.Section4.A04.Cgron_pos
    regularizedNormDerivative := fun ν a f T hν ha hf w hpath m hm t ht ζ hζ =>
      NSFormalization.Section4.A04.regularizedNormDerivative ν a f T hν ha hf
        (uniqueness_toA02 w) hpath m hm t ht ζ hζ
    highContinuationIntegral := fun ν a f T hν ha hf hf1 w hpath m hm t₀ t ht₀ htt htT =>
      NSFormalization.Section4.A04.highContinuationIntegral ν a f T hν ha hf hf1
        (uniqueness_toA02 w) hpath m hm t₀ t ht₀ htt htT }

/-- Bonus (not a contract field): the opaque continuation constant `Cgron` is
`(Chigh m)²/(4ν)`, the value Young's inequality gives, by `rfl` on `A04.Cgron`'s
definition.  The analogue of version one's `energyHighPartial_Chigh_eq_Ctame`; the
contract keeps `Cgron` opaque, so this is a binding-level fact only. -/
theorem energyHighPartialV2_Cgron_eq (m : ℕ) (ν : ℝ) :
    energyHighPartialV2.Cgron m ν = NSFormalization.Section4.A04.Chigh m ^ 2 / (4 * ν) :=
  rfl

/-- Version one is recovered from version two by the inherited projection, and the
recovered record is **definitionally the frozen version-one witness**
`Bindings.energyHighPartial` (this `def` was built as `{ energyHighPartial with … }`).
`Tests.checkedEnergyHighPartial` keeps running against the untouched
`Bindings.energyHighPartial`; this `rfl` rules out a version two that quietly drops or
weakens a version-one field, which would make the projection fail to be that witness. -/
theorem energyHighPartial_of_v2 :
    energyHighPartialV2.toEnergyHighPartialAPI = energyHighPartial := rfl

end BlowupDensity.Bindings
