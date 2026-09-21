import Bindings.HomogeneousPartialV2

/-!
# B02 `homogeneous_partial_v2` conformance (lane 116)

The version-two homogeneous-approximation contract
`Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API` — version one
extended by the two post-freeze fields `separatedAssembly` (lane 103) and
`approxCompactHomogeneous` (lane 110) — inhabited by `Bindings.homogeneousPartialV2`,
with:

* the two new field types transcribed in the `Contracts.V1.Data` /
  `Contracts.V1.BochnerPartial` vocabulary and inhabited by the projections of the
  binding (so the fields are exactly the spec shapes, not weaker ones);
* `homogeneousPartial_of_v2 : HomogeneousApproxPartialAPI`, the version-one
  projection, confirming no version-one field was dropped or weakened;
* `#print axioms` for the binding, the projection and the two new fields'
  underlying theorems — every one exactly `[propext, Classical.choice, Quot.sound]`.

Checked with
`cd verification && lake env lean ../research/B02/axioms_contract_v2.lean`.

The field `separatedAssembly` is registered with the honest hypothesis `-3/2 < s`
(not the spec's `∀ s`, which is unproved; `REVIEW_APPROX_COMPACT.md` finding 5-A),
and `approxCompactHomogeneous` is registered verbatim as `research/B02/Spec.lean:618`
— definitionally equal to the proving theorem, kernel-checked by `rfl` in
`research/B02/axioms_approx_compact.lean`.  `annularPathApprox` stays excluded.
-/

noncomputable section

open BlowupDensity
open Set MeasureTheory
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ContDiff ENNReal

-- The version-two witness inhabits the version-two API.
example : Contracts.V2.HomogeneousPartial.HomogeneousApproxPartialV2API :=
  BlowupDensity.Bindings.homogeneousPartialV2

-- Version one is recovered by the inherited projection: no field dropped or weakened.
example : Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI :=
  BlowupDensity.Bindings.homogeneousPartial_of_v2

-- `separatedAssembly` (research/B02/Spec.lean:593) on `-3/2 < s`, in contract
-- vocabulary, inhabited by the binding's field.
example : ∀ (s : ℝ), -3 / 2 < s → ∀ (J : ℕ) (φ : Fin J → ℝ → ℝ)
    (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
    (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
    (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
    (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
    (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) →
    MemForceCompact (Contracts.V1.BochnerPartial.separatedField φ h) ∧
      IsHomogeneousPath s (Contracts.V1.BochnerPartial.separatedField φ h)
        (Contracts.V1.BochnerPartial.separatedPath φ A) ∧
      AEStronglyMeasurable
        (Contracts.V1.BochnerPartial.separatedPath φ A) forceTimeMeasure :=
  BlowupDensity.Bindings.homogeneousPartialV2.separatedAssembly

-- `approxCompactHomogeneous` (research/B02/Spec.lean:618) verbatim, in contract
-- vocabulary, inhabited by the binding's field.
example : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ,
    Contracts.V1.HomogeneousPartial.SplitRange s →
    CompletedDenseHomogeneous q s forceClassCompact :=
  BlowupDensity.Bindings.homogeneousPartialV2.approxCompactHomogeneous

/-! ## Axiom audit — every declaration is exactly `[propext, Classical.choice, Quot.sound]` -/

#print axioms BlowupDensity.Bindings.homogeneousPartialV2
#print axioms BlowupDensity.Bindings.homogeneousPartial_of_v2
#print axioms NSFormalization.Section4.B02.separatedAssembly
#print axioms NSFormalization.Section4.B02.approxCompactHomogeneous
