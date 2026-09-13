import Contracts.V1.Data
import NSFormalization.Section4.B02.SeparatedAssembly

/-!
# B02 `separatedAssembly` conformance (lane 103)

The spec field `research/B02/Spec.lean:582-600` `separatedAssembly` of `HomogeneousApproxAPI`,
transcribed in the `Contracts.V1.Data` vocabulary (with the spec-local `separatedField` /
`separatedPath` restated verbatim from `Spec.lean:217,229`), inhabited by
`NSFormalization.Section4.B02.separatedAssembly`, followed by `#print axioms` for every public
declaration.  Checked with
`cd verification && lake env lean ../research/B02/axioms_separated.lean`.

**Not the verbatim field.**  The theorem — and hence the `example` below — carries the extra
hypothesis `-3 / 2 < s`; the spec field quantifies over all real `s`.  See
`NSFormalization.Section4.B02.SeparatedAssembly`'s module docstring and
`research/B02/ATTEMPTS_SEPARATED.md`.  The extra hypothesis is placed immediately after `s`; every
other token is the spec field.  It typechecks because each restated predicate in
`Section4/{B01/Separated, D01/HomogeneousWitness}.lean` is definitionally equal to its
`Contracts.V1.Data` counterpart, and the two `separatedField` / `separatedPath` `def`s are equal.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

/-- `research/B02/Spec.lean:217`, restated verbatim: the physical spacetime field assembled from
smooth compact time factors `φ` and spatial profiles `h`.  The same `def` as
`research/B01/Spec.lean:140`. -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    SpaceTimeField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- `research/B02/Spec.lean:229`, restated verbatim: the order-`s` datum path of
`separatedField φ h`.  The same `def` as `research/B01/Spec.lean:147`. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

-- `separatedAssembly` (`Spec.lean:582`): the spec field type in the `Contracts.V1.Data` vocabulary,
-- with the extra hypothesis `-3 / 2 < s` immediately after `s` (see the header), inhabited by the
-- `B02` theorem through the definitional bridges.
example : ∀ (s : ℝ), -3 / 2 < s → ∀ (J : ℕ) (φ : Fin J → ℝ → ℝ)
    (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
    (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
    (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
    (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
    (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) →
  MemForceCompact (separatedField φ h) ∧
    IsHomogeneousPath s (separatedField φ h) (separatedPath φ A) ∧
    AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure :=
  fun s hs _ φ h A hφs hφc hφpos hhs hhc hA =>
    NSFormalization.Section4.B02.separatedAssembly s hs φ h A hφs hφc hφpos hhs hhc hA

/-! ## Axiom audit — every public declaration is exactly `[propext, Classical.choice, Quot.sound]` -/

#print axioms NSFormalization.Section4.B02.schwartzAngularFourier_finsetSum_smul
#print axioms NSFormalization.Section4.B02.homogeneousProfile_finsetSum_smul_apply
#print axioms NSFormalization.Section4.B02.homogeneousDatum_finsetSum_smul
#print axioms NSFormalization.Section4.B02.hasCompactSupport_sum_smul
#print axioms NSFormalization.Section4.B02.isHomogeneousSliceDatum_sum_smul
#print axioms NSFormalization.Section4.B02.separatedAssembly

end
