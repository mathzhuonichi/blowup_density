import Contracts.V1.Data
import NSFormalization.Section4.B02.ApproxCompact

/-!
# B02 `approxCompactHomogeneous` conformance (lane 110)

The final field of `research/B02/Spec.lean`'s `HomogeneousApproxAPI`,
`approxCompactHomogeneous` (`Spec.lean:607`), and the intermediate export
`SeparatedCompactHomogeneousDense` (`Spec.lean:653-664`), transcribed in the
`Contracts.V1.Data` vocabulary (with the spec-local `separatedField`,
`separatedPath`, `SplitRange` restated verbatim from `Spec.lean:206,219,237`),
each inhabited by the `NSFormalization.Section4.B02` theorem of `ApproxCompact.lean`,
followed by `#print axioms` for every public declaration.  Checked with
`cd verification && lake env lean ../research/B02/axioms_approx_compact.lean`.

The `example`s typecheck because each restated predicate of
`Section4/{B01/Separated, B01/Compact, D01/ForceClass, D01/HomogeneousWitness,
B02/Cutoff}` is definitionally equal to its `Contracts.V1.Data` counterpart, the
two `separatedField` / `separatedPath` `def`s are equal, and `SplitRange` and
`Data.SpatialField` (= `Space → Space`) are literal.

`approxCompactHomogeneous` is **definitionally equal** to the spec field
(`Spec.lean:607`) under those equalities — not literally token-identical, since
`Spec.lean:607` writes `CompletedDenseHomogeneous` (the `Data.lean:752` `abbrev`
for `CompletedDenseVia q s (IsHomogeneousPath s)`) and the spec-local `SplitRange`
where the lane uses the `formalization/` `CompletedDenseVia` / `IsHomogeneousPath`
/ `forceClassCompact` / `SplitRange` restatements.  The defeq is confirmed **by the
kernel** via `example : specApproxCompactHomogeneous = laneApproxCompactHomogeneous
:= rfl` below (stronger than the elaboration-unification the conformance `example`s
rely on).  `SeparatedCompactHomogeneousDense` carries the theorem's hypotheses
`1 ≤ q`, `q ≠ ⊤`, `SplitRange s` (which the `def` of `Spec.lean:653` does not,
being an unconditional predicate); the `example` below therefore inhabits the spec
`def`'s *body* on those hypotheses, which is exactly the shape
`approxCompactHomogeneous` consumes.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space SpaceTime)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

/-- `research/B02/Spec.lean:206`, restated verbatim. -/
def separatedField {J : ℕ} (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField) :
    SpaceTimeField :=
  fun z => ∑ j, φ j z.1 • h j z.2

/-- `research/B02/Spec.lean:219`, restated verbatim. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-- `research/B02/Spec.lean:237`, restated verbatim. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

-- `SeparatedCompactHomogeneousDense` (`Spec.lean:653`): the spec `def`'s body in the
-- `Contracts.V1.Data` vocabulary, on the theorem's hypotheses, inhabited by the `B02` theorem.
example (q : ℝ≥0∞) (hq1 : 1 ≤ q) (hqt : q ≠ ⊤) (s : ℝ) (hs : SplitRange s) :
    ∀ (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
      ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (h : Fin J → SpatialField)
        (A : Fin J → RealVectorSobolev s),
        (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
        (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
        (∀ j, ContDiff ℝ ∞ (h j)) ∧ (∀ j, HasCompactSupport (h j)) ∧
        (∀ j, IsHomogeneousSliceDatum s (h j) (A j)) ∧
        MemForceCompact (separatedField φ h) ∧
        IsHomogeneousPath s (separatedField φ h) (separatedPath φ A) ∧
        AEStronglyMeasurable (separatedPath φ A) forceTimeMeasure ∧
        bochnerDatumENorm q s (separatedPath φ A - b) < η :=
  NSFormalization.Section4.B02.separatedCompactHomogeneousDense q hq1 hqt s hs

-- `approxCompactHomogeneous` (`Spec.lean:607`): the spec field type in the
-- `Contracts.V1.Data` vocabulary, inhabited by the `B02` theorem.
example : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, SplitRange s →
    CompletedDenseHomogeneous q s forceClassCompact :=
  fun q hq1 hqt s hs => NSFormalization.Section4.B02.approxCompactHomogeneous q hq1 hqt s hs

/-- The spec field type verbatim (`Spec.lean:607`), `Contracts.V1.Data` vocabulary. -/
def specApproxCompactHomogeneous : Prop :=
  ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, SplitRange s →
    CompletedDenseHomogeneous q s forceClassCompact

/-- The lane theorem's type verbatim, `formalization/` vocabulary. -/
def laneApproxCompactHomogeneous : Prop :=
  ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ, NSFormalization.Section4.B02.SplitRange s →
    NSFormalization.Section4.B01.CompletedDenseVia q s
      (NSFormalization.Section4.D01.Homogeneous.IsHomogeneousPath s)
      NSFormalization.Section4.B01.forceClassCompact

-- Kernel-checked definitional equality of the two type strings (finding 2-A): the
-- three token differences (`CompletedDenseHomogeneous` abbrev, `SplitRange`,
-- `forceClassCompact`) are all defeq, so the spec field and the lane theorem are the
-- same proposition on the nose.
example : specApproxCompactHomogeneous = laneApproxCompactHomogeneous := rfl

-- …and the lane theorem does have that type.
example : laneApproxCompactHomogeneous := NSFormalization.Section4.B02.approxCompactHomogeneous

/-! ## Axiom audit — every public declaration is exactly `[propext, Classical.choice, Quot.sound]` -/

#print axioms NSFormalization.Section4.B02.eLpNorm_smul_const
#print axioms NSFormalization.Section4.B02.bochnerDatumENorm_separatedPath_sub_le
#print axioms NSFormalization.Section4.B02.SeparatedCompactHomogeneousDense
#print axioms NSFormalization.Section4.B02.separatedCompactHomogeneousDense
#print axioms NSFormalization.Section4.B02.approxCompactHomogeneous

end
