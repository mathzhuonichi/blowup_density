import Contracts.V1.Data
import NSFormalization.Section4.B01.Separated
import NSFormalization.Section4.B01.Spatial

/-!
# B01 units 6 and 8 conformance

`example` blocks whose types are the `BochnerApproxAPI` fields `separatedAssembly`
(`research/B01/Spec.lean:292`, unit 6) and `spatialApprox` (`research/B01/Spec.lean:250`, unit 8),
each discharged by the theorems of `NSFormalization.Section4.B01.{Separated,Spatial}`, followed by
`#print axioms`.  Checked with `cd verification && lake env lean ../research/B01/axioms_u68.lean`.

The field types are transcribed from `research/B01/Spec.lean` in the namespace it uses
(`open BlowupDensity.Contracts.V1.Data`, `NavierStokes.ProblemStatement (Space)`,
`NSFormalization.Paper3 (RealVectorSobolev)`), with the Spec-local definitions `separatedField`
and `separatedPath` (`Spec.lean:140,147`) restated verbatim.  The examples typecheck because each
restated predicate in the formalization modules is definitionally equal to its
`Contracts.V1.Data` counterpart.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

/-- `research/B01/Spec.lean:140`, restated. -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    SpaceTimeField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- `research/B01/Spec.lean:147`, restated. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-! ## Unit 6: `separatedAssembly` (`research/B01/Spec.lean:292`) -/

example : ∀ (s : ℝ) (J : ℕ) (φ : Fin J → ℝ → ℝ)
    (h : Fin J → SpatialField) (A : Fin J → RealVectorSobolev s),
    (∀ j, ContDiff ℝ ∞ (φ j)) → (∀ j, HasCompactSupport (φ j)) →
    (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) →
    (∀ j, ContDiff ℝ ∞ (h j)) → (∀ j, HasCompactSupport (h j)) →
    (∀ j, IsSobolevDatum s (h j) (A j)) →
    MemForceCompact (separatedField φ h) ∧
      IsSobolevPath s (separatedField φ h) (separatedPath φ A) ∧
      AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure :=
  fun s _J φ h A hφs hφc hφpos hhs hhc hA =>
    NSFormalization.Section4.B01.separatedAssembly s φ h A hφs hφc hφpos hhs hhc hA

/-! ## Unit 8: `spatialApprox` (`research/B01/Spec.lean:250`) -/

example : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (h : SpatialField) (H : RealVectorSobolev s),
      ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsSobolevDatum s h H ∧ ‖H - A‖ₑ < η :=
  fun s A η hη => NSFormalization.Section4.B01.spatialApprox s A η hη

/-! ## Axiom audit -/

#print axioms NSFormalization.Section4.B01.separatedAssembly
#print axioms NSFormalization.Section4.B01.spatialApprox

end
