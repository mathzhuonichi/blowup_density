import Contracts.V1.EnergyAbsorptionPartial
import Bindings.Uniqueness
import Bindings.GradientL6
import NSFormalization.Section4.C01.VelocityJets
import NSFormalization.Section4.C01.ForceSlices
import NSFormalization.Section4.C01.Trilinear

/-! The only layer that knows the current implementation's names and paths for the
proved part of the ordinary-energy and `H¹`-absorption *a priori* interface of C01.

`Contracts.V1.EnergyAbsorptionPartial` is self-contained — its only imports are
two other contracts, `Contracts.V1.Data` and `Contracts.V1.GradientL6` — so this
adapter has two jobs: record by `rfl` that each spec-local time-slice `def` the
specification restates is the notion the proof modules use, and assemble the
proved theorems into the contract.

The five proved fields are the theorems of
`NSFormalization.Section4.C01.{VelocityJets,ForceSlices,Trilinear}` verbatim
(defeq bridges the contract's `Data`/`GradientL6` vocabulary to the modules'
token-for-token restatements, exactly as the conformance files
`research/C01/axioms_u1u3.lean`, `axioms_u2.lean` and `axioms_u6.lean` check):

* `velocityJets` — `velocity_slice_memHInfty_and_smoothL2`, applied to the
  solution moved across the two `ClassicalSolutionR` copies by the reused
  `Bindings.uniqueness_toA02` (`Contracts.V1.Data.ClassicalSolutionR` and the
  `Section4/A02` restatement are distinct inductive types, so a `rfl` bridge for
  the structure itself is impossible; each field type is defeq, so the field-wise
  conversion typechecks).  The conclusion's two predicates are drift-guarded by
  `rfl` bridges: `MemHInfty` by `energyAbsorptionPartial_memHInfty_eq` below (the
  fourth of the A02-local family `Bindings/Uniqueness.lean` §0 records) and
  `SmoothSquareIntegrableJets` by `Bindings.GradientL6.smoothSquareIntegrableJets_eq`.
* `forceTimeRegularity` — the same-named theorem, assigned directly (the local
  `slice`/`l2Norm` are definitionally the contract's).
* `trilinearHolder`, `trilinearAbsorbed`, `laplacianSqENorm` — the same-named
  theorems.  `C₁` is bound to the registered `A05.gradient_l6`'s constant
  `gradientL6.Csix`, so `trilinearAbsorbed`'s `ENNReal.ofReal C₁` is
  definitionally the theorem's `ENNReal.ofReal gradientL6Const` (the exact defeq
  `research/C01/axioms_u6.lean` exercises).

Every declaration here carries an `energyAbsorptionPartial_` prefix;
`BlowupDensity.Bindings` is a flat namespace shared by all adapters. -/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ENNReal

section Correspondence

/-- The contract's `H^∞` datum class is the `Section4/A02` restatement — the
fourth of the A02-local family `Bindings/Uniqueness.lean` §0 records
(`initialClassR`, `MemForceR`, `PressureGaugeEquivOn`).  It drift-guards the
`MemHInfty` conjunct of `velocityJets`'s conclusion. -/
theorem energyAbsorptionPartial_memHInfty_eq (a : Contracts.V1.Data.SpatialField) :
    Contracts.V1.Data.MemHInfty a = NSFormalization.Section4.A02.MemHInfty a := rfl

/-- The contract's slice is the implementation's. -/
theorem energyAbsorptionPartial_slice_eq :
    Contracts.V1.EnergyAbsorptionPartial.slice = NSFormalization.Section4.C01.slice := rfl

/-- The contract's `l2Sq` is the implementation's. -/
theorem energyAbsorptionPartial_l2Sq_eq :
    Contracts.V1.EnergyAbsorptionPartial.l2Sq = NSFormalization.Section4.C01.l2Sq := rfl

/-- The contract's `l2Norm` is the implementation's. -/
theorem energyAbsorptionPartial_l2Norm_eq :
    Contracts.V1.EnergyAbsorptionPartial.l2Norm = NSFormalization.Section4.C01.l2Norm := rfl

/-- The contract's `laplacianSq` is the implementation's. -/
theorem energyAbsorptionPartial_laplacianSq_eq :
    Contracts.V1.EnergyAbsorptionPartial.laplacianSq
      = NSFormalization.Section4.C01.laplacianSq := rfl

/-- The contract's `criticalL3` is the implementation's. -/
theorem energyAbsorptionPartial_criticalL3_eq :
    Contracts.V1.EnergyAbsorptionPartial.criticalL3
      = NSFormalization.Section4.C01.criticalL3 := rfl

/-- The contract's `advectionWork` is the implementation's (via the `rfl` bridges
`Contracts.V1.lift`/`laplacian` = the A05 objects, recorded in
`Bindings.GradientL6`). -/
theorem energyAbsorptionPartial_advectionWork_eq :
    Contracts.V1.EnergyAbsorptionPartial.advectionWork
      = NSFormalization.Section4.C01.advectionWork := rfl

end Correspondence

/-- Bind the proved fields of the ordinary-energy and `H¹`-absorption interface to
the stable version-one contract. -/
def energyAbsorptionPartial :
    Contracts.V1.EnergyAbsorptionPartial.EnergyAbsorptionPartialAPI where
  C₁ := gradientL6.Csix
  C₁_pos := gradientL6.Csix_pos
  velocityJets := fun _ _ _ _ _ _ _ w _ ht =>
    NSFormalization.Section4.C01.velocity_slice_memHInfty_and_smoothL2
      (uniqueness_toA02 w) ht
  forceTimeRegularity := NSFormalization.Section4.C01.forceTimeRegularity
  trilinearHolder := fun z hz => NSFormalization.Section4.C01.trilinearHolder z hz
  trilinearAbsorbed := fun z hz => NSFormalization.Section4.C01.trilinearAbsorbed z hz
  laplacianSqENorm := fun z hz => NSFormalization.Section4.C01.laplacianSqENorm z hz

end BlowupDensity.Bindings
