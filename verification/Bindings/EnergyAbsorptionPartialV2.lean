import Contracts.V2.EnergyAbsorptionPartial
import Bindings.EnergyAbsorptionPartial
import Bindings.Uniqueness
import NSFormalization.Section4.C01.EnergySpec

/-! The implementation layer for the version-two energy-absorption-partial contract, and the
compatibility bridge back to version one.

`Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API` extends
`Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI` by the single field
`energyIdentity`, discharged by `NSFormalization.Section4.C01.energyIdentity_l2Sq`
(`Section4/C01/EnergySpec.lean`, the clamp-free `l2Sq`/`slice`/`pairing` form of lane 150's
`energyIdentity_classical_unconditional`).  This file has these jobs.

* `energyAbsorptionPartialV2` inhabits the version-two record.  It reuses the frozen
  version-one witness `Bindings.energyAbsorptionPartial` with `{ … with … }` and fills
  `energyIdentity` with the `Section4/C01` theorem, transported across the two
  `ClassicalSolutionR` copies by the reused `Bindings.uniqueness_toA02` exactly as the V1
  `velocityJets` does (`(uniqueness_toA02 w).velocity = w.velocity` by `rfl`; `w.velocity` is
  the only projection the statement mentions).  The contract's `0 < ν` and `a ∈ initialClassR`
  are **unused** — the lane's theorem is stronger (it needs neither).
* `energyAbsorptionPartialV2_pairing_eq` records by `rfl` that the contract's `pairing`
  (`Contracts/V2/EnergyAbsorptionPartial.lean`) is the implementation's
  `NSFormalization.Section4.C01.pairing` (both `∫ x, ⟪w x, z x⟫`) — the **new** `rfl` bridge
  of this contract, alongside the V1 `slice`/`l2Sq` bridges the field also uses defeq.
* `energyAbsorptionPartialV2_gradientSq_eq` is the **single non-`rfl` bridge**: the contract's
  `gradientSq z = ∫|gradientTensor z|²` equals the raw Frobenius integrand
  `∫∑ᵢ‖∂ᵢz‖²` the lane's theorem produces, by `PiLp.norm_sq_eq_of_L2` (pointwise) fed through
  `integral_congr_ae` (exactly `research/C01/probes/rev150b_gradientsq.lean`).  This is the
  whole of the `formalization → contract` vocabulary debt for `energyIdentity`.
* `energyAbsorptionPartial_of_v2` records by `rfl` that the inherited version-one projection
  is the frozen version-one witness `Bindings.energyAbsorptionPartial`.

Every declaration carries an `energyAbsorptionPartial`/`energyAbsorptionPartialV2` prefix;
`BlowupDensity.Bindings` is a flat namespace shared by all adapters. -/

noncomputable section

namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1 (lift gradientTensor)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal

section Correspondence

/-- **The new `rfl` bridge.**  The contract's `pairing`
(`Contracts/V2/EnergyAbsorptionPartial.lean`) is the implementation's
`NSFormalization.Section4.C01.pairing` (`Section4/C01/EnergySpec.lean`); both are
`fun w z => ∫ x, (inner ℝ (w x) (z x) : ℝ)`, and `SpatialField` is defeq to A02's. -/
theorem energyAbsorptionPartialV2_pairing_eq :
    Contracts.V2.EnergyAbsorptionPartial.pairing
      = NSFormalization.Section4.C01.pairing := rfl

/-- Pointwise: the squared norm of the gradient **tensor** is the raw Frobenius sum the
`formalization` side produces.  One `PiLp.norm_sq_eq_of_L2`, then `rfl` absorbs
`spatialDerivative (lift z) 0 x = fderiv ℝ z x` and `axis i = coordinateVector i`
(`research/C01/probes/rev150b_gradientsq.lean`). -/
theorem energyAbsorptionPartialV2_gradientTensor_normSq (z : SpatialField) (x : Space) :
    ‖gradientTensor z x‖ ^ 2 = ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2 := by
  rw [gradientTensor, spatialGradient, PiLp.norm_sq_eq_of_L2]
  rfl

/-- **The single non-`rfl` bridge of this contract.**  The contract's `gradientSq z`
(`= ∫ x, ‖gradientTensor z x‖²`) equals the raw gradient integrand
`∫ x, ∑ᵢ‖∂ᵢz‖²` of `energyIdentity_l2Sq`, by the pointwise identity above fed through
`integral_congr_ae`. -/
theorem energyAbsorptionPartialV2_gradientSq_eq (z : SpatialField) :
    Contracts.V2.EnergyAbsorptionPartial.gradientSq z
      = ∫ x : Space, ∑ i : Fin 3, ‖fderiv ℝ z x (coordinateVector i)‖ ^ 2 := by
  show (∫ x : Space, ‖gradientTensor z x‖ ^ 2) = _
  exact integral_congr_ae
    (Filter.Eventually.of_forall (energyAbsorptionPartialV2_gradientTensor_normSq z))

end Correspondence

/-- Bind the version-two contract: version one's frozen witness plus the ordinary energy
identity.  The record carries a data field (`C₁`, inherited), so this is a `def`, as in
version one.  `energyIdentity` rewrites the contract's `gradientSq` to the raw gradient
integrand (the one non-`rfl` bridge) and then closes by the `Section4/C01` theorem; the
`l2Sq`/`slice`/`pairing` vocabulary and `(uniqueness_toA02 w).velocity = w.velocity` are all
defeq, so no further rewriting is needed.  The contract hypotheses `0 < ν` (the anonymous
`_`) and `a ∈ initialClassR` (`_`) are unused: the lane's theorem is stronger. -/
def energyAbsorptionPartialV2 :
    Contracts.V2.EnergyAbsorptionPartial.EnergyAbsorptionPartialV2API :=
  { energyAbsorptionPartial with
    energyIdentity := fun _ _ _ _ _ hf _ w _ ht => by
      rw [energyAbsorptionPartialV2_gradientSq_eq]
      exact NSFormalization.Section4.C01.energyIdentity_l2Sq (uniqueness_toA02 w) hf ht }

/-- Version one is recovered from version two by the inherited projection, and the recovered
record is **definitionally the frozen version-one witness** `Bindings.energyAbsorptionPartial`
(this `def` was built as `{ energyAbsorptionPartial with … }`).
`Tests.checkedEnergyAbsorptionPartial` keeps running against the untouched
`Bindings.energyAbsorptionPartial`; this `rfl` rules out a version two that quietly drops or
weakens a version-one field. -/
theorem energyAbsorptionPartial_of_v2 :
    energyAbsorptionPartialV2.toEnergyAbsorptionPartialAPI = energyAbsorptionPartial := rfl

end BlowupDensity.Bindings
