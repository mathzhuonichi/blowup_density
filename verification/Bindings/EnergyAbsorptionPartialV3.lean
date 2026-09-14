import Contracts.V3.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartialV2
import NSFormalization.Section4.C01.EnergyBounds

/-! The implementation layer for the version-three energy-absorption-partial contract, and the
compatibility bridge back to version two.

`Contracts.V3.EnergyAbsorptionPartial.EnergyAbsorptionPartialV3API` extends
`Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API` by the two ordinary-energy
consequence fields `energyDifferentialBound` and `l2Bound` (eq:RL2), both discharged by
`Section4/C01/EnergyBounds.lean` (lane 154).  This file has these jobs.

* `energyAbsorptionPartialV3` inhabits the version-three record.  It reuses the frozen
  version-two witness `Bindings.energyAbsorptionPartialV2` with `{ … with … }` and fills the two
  new fields, transported across the two `ClassicalSolutionR` copies by the reused
  `Bindings.uniqueness_toA02` exactly as the V2 `energyIdentity` does
  (`(uniqueness_toA02 w).velocity = w.velocity` by `rfl`).  `l2Bound` binds with **no bridge**:
  the contract's `energyBudget`/`l2Norm`/`slice` vocabulary is defeq to
  `NSFormalization.Section4.C01`'s.  `energyDifferentialBound` binds through **exactly one**
  `rw`, the already-existing V2 `gradientSq` bridge
  `Bindings.energyAbsorptionPartialV2_gradientSq_eq`
  (`Bindings/EnergyAbsorptionPartialV2.lean:70-75`): the contract's `gradientSq z`
  (`= ∫|gradientTensor z|²`) rewrites to the raw Frobenius integrand `∫∑ᵢ‖∂ᵢz‖²` the lane's
  theorem `energyDifferentialBound` produces.  Confirmed end-to-end by the reviewer dry run
  `research/C01/probes/rev154_v3_binding_dryrun.lean`.
* `energyAbsorptionPartialV3_forcePrimitive_eq` / `energyAbsorptionPartialV3_energyBudget_eq`
  record by `rfl` that the contract's two new spec-local `def`s `forcePrimitive`/`energyBudget`
  (`Contracts/V3/EnergyAbsorptionPartial.lean`) are the implementation's
  `NSFormalization.Section4.C01.forcePrimitive`/`energyBudget` (`Section4/C01/EnergyBounds.lean`)
  — CLAUDE.md's "每个重写的定义都要有桥".  The `slice`/`l2Sq`/`l2Norm`/`gradientSq` vocabulary
  the two fields also use are the V1/V2 `rfl`/non-`rfl` bridges, inherited here through
  `Bindings.EnergyAbsorptionPartialV2`.
* `energyAbsorptionPartialV2_of_v3` records by `rfl` that the inherited version-two projection
  is the frozen version-two witness `Bindings.energyAbsorptionPartialV2`.

Every declaration carries an `energyAbsorptionPartialV2`/`energyAbsorptionPartialV3` prefix;
`BlowupDensity.Bindings` is a flat namespace shared by all adapters. -/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.EnergyAbsorptionPartial (slice l2Sq l2Norm)
open BlowupDensity.Contracts.V2.EnergyAbsorptionPartial (gradientSq)

section Correspondence

/-- **A `rfl` bridge.**  The contract's `forcePrimitive`
(`Contracts/V3/EnergyAbsorptionPartial.lean`) is the implementation's
`NSFormalization.Section4.C01.forcePrimitive` (`Section4/C01/EnergyBounds.lean`); both are
`fun f t => ∫ s in (0 : ℝ)..t, l2Norm (slice f s)`, and `SpaceTimeField` is defeq to A02's. -/
theorem energyAbsorptionPartialV3_forcePrimitive_eq :
    Contracts.V3.EnergyAbsorptionPartial.forcePrimitive
      = NSFormalization.Section4.C01.forcePrimitive := rfl

/-- **A `rfl` bridge.**  The contract's `energyBudget`
(`Contracts/V3/EnergyAbsorptionPartial.lean`) is the implementation's
`NSFormalization.Section4.C01.energyBudget` (`Section4/C01/EnergyBounds.lean`); both are
`fun a f t => l2Norm a + forcePrimitive f t`. -/
theorem energyAbsorptionPartialV3_energyBudget_eq :
    Contracts.V3.EnergyAbsorptionPartial.energyBudget
      = NSFormalization.Section4.C01.energyBudget := rfl

end Correspondence

/-- Bind the version-three contract: version two's frozen witness plus the two ordinary-energy
consequences.  The record carries a data field (`C₁`, inherited), so this is a `def`, as in
versions one and two.  `energyDifferentialBound` rewrites the contract's `gradientSq` to the raw
gradient integrand (the one V2 non-`rfl` bridge) and then closes by the `Section4/C01` theorem;
`l2Bound` closes by the `Section4/C01` theorem directly (no bridge).  In both, the
`l2Sq`/`slice`/`l2Norm`/`energyBudget` vocabulary and `(uniqueness_toA02 w).velocity = w.velocity`
are all defeq.  The contract hypotheses `a ∈ initialClassR` (the anonymous `_`) are unused in
both fields, and `0 < ν` is unused in `energyDifferentialBound`; `l2Bound` consumes `0 < ν` as
`hν`. -/
def energyAbsorptionPartialV3 :
    Contracts.V3.EnergyAbsorptionPartial.EnergyAbsorptionPartialV3API :=
  { energyAbsorptionPartialV2 with
    energyDifferentialBound := fun _ _ _ _ _ hf _ w _ ht E' hderiv => by
      rw [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.energyDifferentialBound (uniqueness_toA02 w) hf ht E'
        hderiv
    l2Bound := fun _ hν _ _ _ hf _ w _ ht =>
      NSFormalization.Section4.C01.l2Bound (uniqueness_toA02 w) hf hν ht }

/-- Version two is recovered from version three by the inherited projection, and the recovered
record is **definitionally the frozen version-two witness** `Bindings.energyAbsorptionPartialV2`
(this `def` was built as `{ energyAbsorptionPartialV2 with … }`).
`Tests.checkedEnergyAbsorptionPartialV2` keeps running against the untouched
`Bindings.energyAbsorptionPartialV2`; this `rfl` rules out a version three that quietly drops or
weakens a version-two (hence version-one) field. -/
theorem energyAbsorptionPartialV2_of_v3 :
    energyAbsorptionPartialV3.toEnergyAbsorptionPartialV2API = energyAbsorptionPartialV2 := rfl

end BlowupDensity.Bindings
