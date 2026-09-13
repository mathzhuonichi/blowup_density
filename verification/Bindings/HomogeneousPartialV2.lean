import Contracts.V2.HomogeneousPartial
import Bindings.HomogeneousPartial
import NSFormalization.Section4.B02.SeparatedAssembly
import NSFormalization.Section4.B02.ApproxCompact

/-! The implementation layer for the version-two homogeneous-partial contract, and
the compatibility bridge back to version one.

`Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API` extends
`Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI` by the two fields
`separatedAssembly` (lane 103, `NSFormalization.Section4.B02.separatedAssembly`) and
`approxCompactHomogeneous` (lane 110,
`NSFormalization.Section4.B02.approxCompactHomogeneous`), so this file has two jobs.

* `homogeneousPartialV2` inhabits the version-two record.  It reuses the frozen
  version-one witness `Bindings.homogeneousPartial` with `{ … with … }` and fills
  the two new fields with the two `Section4/B02` theorems, assigned **directly**:
  no transport is needed because the contract states both fields in the shared
  `Contracts.V1.Data`/`Contracts.V1.BochnerPartial` vocabulary, which is
  definitionally equal to the `formalization/` vocabulary the theorems use.
* `homogeneousPartial_of_v2` records that version one is recoverable from version
  two by the inherited projection `toHomogeneousApproxPartialAPI`; the recovery is
  definitional, so it cannot drift, and `Tests.checkedHomogeneousPartial` keeps
  using the untouched `Bindings.homogeneousPartial`.

## Why the two assignments are direct (no new bridge)

The version-two contract restates no new object, so §1's `rfl` bridges are the ones
already recorded, reused here only for documentation:

* `separatedAssembly`.  `NSFormalization.Section4.B02.separatedAssembly`
  (`SeparatedAssembly.lean:211`) concludes in
  `NSFormalization.Section4.D01.MemForceCompact (Section4.B01.separatedField φ h)`,
  `IsHomogeneousPath` and `NSFormalization.Section4.D01.forceTimeMeasure`; the
  contract asks for the `Contracts.V1.Data` counterparts on
  `Contracts.V1.BochnerPartial.separatedField`/`separatedPath`.  `separatedField`
  and `separatedPath` are `= NSFormalization.Section4.B01.·` by `rfl`
  (`Bindings/BochnerPartial.lean:47-54`, reused verbatim by version one's
  `separatedAssembly`), and `MemForceCompact`, `IsHomogeneousPath`,
  `forceTimeMeasure` are the same `Data` notions version one's binding already
  discharges the B01 `separatedAssembly` against — so the theorem inhabits the field
  on the nose.  The field's explicit `J` is bound as `_J` and inferred from `φ`, as
  in `Bindings/BochnerPartial.lean:74`.
* `approxCompactHomogeneous`.  `NSFormalization.Section4.B02.approxCompactHomogeneous`
  (`ApproxCompact.lean:229`) is **definitionally equal** to the spec field
  (`research/B02/axioms_approx_compact.lean` proves
  `specApproxCompactHomogeneous = laneApproxCompactHomogeneous := rfl` at the
  kernel), so the `SplitRange s` hypothesis passes through unchanged
  (`SplitRange = NSFormalization.Section4.B02.SplitRange` by `rfl`,
  `Bindings/HomogeneousPartial.lean:97-99`) and the conclusion
  `CompletedDenseHomogeneous q s forceClassCompact` unfolds to the theorem's
  `CompletedDenseVia q s (IsHomogeneousPath s) forceClassCompact`.

Every declaration carries a `homogeneousPartial_` prefix; `BlowupDensity.Bindings`
is a flat namespace shared by all adapters. -/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

section Correspondence

variable {s : ℝ} {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → Contracts.V1.Data.SpatialField)
  (A : Fin J → RealVectorSobolev s)

/-- The two new fields are stated over the shared `separatedField`, already recorded
`= NSFormalization.Section4.B01.separatedField` by `rfl`
(`Bindings/BochnerPartial.lean`); re-recorded here so the version-two adapter is
self-documenting. -/
theorem homogeneousPartialV2_separatedField_eq :
    Contracts.V1.BochnerPartial.separatedField φ h
      = NSFormalization.Section4.B01.separatedField φ h := rfl

/-- The shared `separatedPath`, likewise `= NSFormalization.Section4.B01.separatedPath`
by `rfl`. -/
theorem homogeneousPartialV2_separatedPath_eq :
    Contracts.V1.BochnerPartial.separatedPath φ A
      = NSFormalization.Section4.B01.separatedPath φ A := rfl

/-- The contract's `SplitRange` (from `Contracts.V1.HomogeneousPartial`) is the
implementation's, by `rfl`. -/
theorem homogeneousPartialV2_splitRange_eq (s : ℝ) :
    Contracts.V1.HomogeneousPartial.SplitRange s
      = NSFormalization.Section4.B02.SplitRange s := rfl

end Correspondence

/-- Bind the two post-freeze fields of the homogeneous `Ḣ^{-1}` approximation to the
stable version-two contract, on top of the frozen version-one witness. -/
def homogeneousPartialV2 :
    Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API :=
  { homogeneousPartial with
    separatedAssembly := fun s hs _J φ h A hφs hφc hφpos hhs hhc hA =>
      NSFormalization.Section4.B02.separatedAssembly s hs φ h A hφs hφc hφpos hhs hhc hA
    approxCompactHomogeneous := fun q hq1 hqt s hs =>
      NSFormalization.Section4.B02.approxCompactHomogeneous q hq1 hqt s hs }

/-- Version one is recoverable from version two by the inherited projection: a
version-two record *is* a version-one record together with the two new clauses.
Definitional, so it cannot drift.

`Tests.checkedHomogeneousPartial` does not go through this function — the registered
version-one test keeps using the untouched `Bindings.homogeneousPartial`.  What this
declaration rules out is a version two that quietly drops or weakens a version-one
field, which would make the projection fail to typecheck. -/
def homogeneousPartial_of_v2 :
    Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI :=
  homogeneousPartialV2.toHomogeneousApproxPartialAPI

end BlowupDensity.Bindings
