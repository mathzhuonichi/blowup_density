import Contracts.V2.DatumLemmas
import Bindings.DatumLemmas
import NSFormalization.Section4.D01.HalfOrder

/-! The implementation layer for the version-two datum-lemmas contract, and the
compatibility bridge back to version one.

`Contracts.V2.DatumLemmas.DatumLemmasV2API` extends
`Contracts.V1.DatumLemmas.DatumLemmasAPI` by three half-order finiteness fields,
all proved in `NSFormalization.Section4.D01.HalfOrder` (lane 042), so this file
has three jobs.

* `datumLemmasV2` inhabits the version-two record.  It reuses the frozen
  version-one witness `Bindings.datumLemmas` with `{ … with … }` and fills the
  three new fields with the `HalfOrder.lean` theorems directly — no `by` block,
  only argument permutations.
* `datumLemmas_of_v2` records that version one is recoverable from version two by
  the inherited projection `toDatumLemmasAPI`; the recovery is definitional, so
  it cannot drift, and `Tests.checkedDatumLemmas` keeps using the untouched
  `Bindings.datumLemmas`.
* §1's `rfl` bridges pin `HalfOrder.lean`'s local restatements of
  `Contracts.V1.Data.forceSobolevENorm` and `forceSobolevENormL1` to the contract
  declarations, so CI fails if either side drifts.  They follow
  `research/D01/axioms_halforder.lean` (`halforder_forceSobolevENorm_eq`,
  `halforder_forceSobolevENormL1_eq`); `MemForceR`'s bridge already lives in
  `Bindings.DatumLemmas` (`datumLemmas_memForceR_eq`) and is imported, not
  repeated.  `forceSobolevENormL2` has no local copy in `HalfOrder.lean` — it uses
  `forceSobolevENorm 2` directly — so it needs no separate bridge.
-/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement
open scoped ContDiff ENNReal SchwartzMap

/-! ## 1. Correspondence: the restated definitions are the contract's own -/

section Correspondence

variable (q : ℝ≥0∞) (s : ℝ) (f : Contracts.V1.Data.SpaceTimeField)

/-- `HalfOrder.lean:141` is `Data.forceSobolevENorm` (`Data.lean:225`).  Same
bridge as `research/D01/axioms_halforder.lean:22`. -/
theorem datumLemmasV2_forceSobolevENorm_eq :
    NSFormalization.Section4.D01.forceSobolevENorm q s f
      = Contracts.V1.Data.forceSobolevENorm q s f := rfl

/-- `HalfOrder.lean:148` is `Data.forceSobolevENormL1` (`Data.lean:231`).  Same
bridge as `research/D01/axioms_halforder.lean:27`. -/
theorem datumLemmasV2_forceSobolevENormL1_eq :
    NSFormalization.Section4.D01.forceSobolevENormL1 s f
      = Contracts.V1.Data.forceSobolevENormL1 s f := rfl

end Correspondence

/-! ## 2. The contract -/

/-- Bind the proved half-order finiteness lemmas of lane 042 to the stable
version-two contract, on top of the frozen version-one witness.

The three new fields are `Section4/D01/HalfOrder.lean`'s theorems verbatim: the
`rfl` bridges of §1 make `HalfOrder.forceSobolevENorm` and its `q = 1` case
`forceSobolevENormL1` the contract's own `Data.forceSobolevENorm` /
`Data.forceSobolevENormL1`, and `Data.forceSobolevENormL2 (1/2)` is by
definition `Data.forceSobolevENorm 2 (1/2)`, which is
`HalfOrder.forceSobolevENormL2_half_ne_top`'s conclusion. -/
def datumLemmasV2 : Contracts.V2.DatumLemmas.DatumLemmasV2API :=
  { Bindings.datumLemmas with
    forceSobolevENorm_ne_top := fun _ hf _ _ hsm _ hq =>
      NSFormalization.Section4.D01.forceSobolevENorm_ne_top hf hsm hq
    forceSobolevENormL1_half_ne_top := fun _ hf =>
      NSFormalization.Section4.D01.forceSobolevENormL1_half_ne_top hf
    forceSobolevENormL2_half_ne_top := fun _ hf =>
      NSFormalization.Section4.D01.forceSobolevENormL2_half_ne_top hf }

/-- Version one is recoverable from version two by the inherited projection: a
version-two record *is* a version-one record together with the three half-order
clauses.  Definitional, so it cannot drift.

`Tests.checkedDatumLemmas` does not go through this function — the registered
version-one test keeps using the untouched `Bindings.datumLemmas`.  What this
declaration rules out is a version two that quietly drops or weakens a
version-one field, which would make the projection fail to typecheck. -/
def datumLemmas_of_v2 : Contracts.V1.DatumLemmas.DatumLemmasAPI :=
  datumLemmasV2.toDatumLemmasAPI

end BlowupDensity.Bindings
