import Contracts.V1.Data
import NSFormalization.Section4.B01.Compact
import NSFormalization.Section4.B01.Completion

/-!
# B01 units 1–3 conformance

`example` blocks whose types are the `BochnerApproxAPI` fields of `research/B01/Spec.lean`
(units 2 and 3) and the unit-1 obligations of `research/B01/COMPARISON.md:145`, each discharged
by the theorems of `NSFormalization.Section4.B01.{Compact,Completion}`, followed by
`#print axioms` for every theorem.  Checked with `cd verification && lake env lean
../research/B01/axioms_u123.lean`.

The field types below are transcribed from `research/B01/Spec.lean:219-338` in the namespace it
uses (`open BlowupDensity.Contracts.V1.Data`, `NavierStokes.ProblemStatement (Space)`,
`NSFormalization.Paper3 (RealVectorSobolev)`), with the Spec-local abbreviation `bochnerSpace`
restated verbatim (`Spec.lean:158`).  The examples typecheck because each restated predicate in
the formalization modules is definitionally equal to its `Contracts.V1.Data` counterpart.
-/

noncomputable section

open MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

/-- `research/B01/Spec.lean:158`, restated. -/
noncomputable abbrev bochnerSpace (q : ℝ≥0∞) (s : ℝ) :=
  Lp (RealVectorSobolev s) q forceTimeMeasure

/-! ## Unit 1 (helper obligations of `research/B01/COMPARISON.md:145`) -/

-- `IsSobolevPath` half: the datum path of the components of a compact smooth field.
example : ∀ (s : ℝ) (F : SpaceTimeField) (f : Fin 3 → ℝ × Space → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i)),
    (∀ z i, (F z).ofLp i = f i z) →
    IsSobolevPath s F (NSFormalization.Paper3.angularRealVectorSlice s f hf hc) :=
  fun s F f hf hc hFf =>
    NSFormalization.Section4.B01.isSobolevPath_angularRealVectorSlice s F f hf hc hFf

-- `AEStronglyMeasurable` half.
example : ∀ (s : ℝ) (f : Fin 3 → ℝ × Space → ℝ)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hc : ∀ i, HasCompactSupport (f i)),
    AEStronglyMeasurable (NSFormalization.Paper3.angularRealVectorSlice s f hf hc)
      forceTimeMeasure :=
  fun s f hf hc =>
    NSFormalization.Section4.B01.aestronglyMeasurable_angularRealVectorSlice s f hf hc

-- `MemForceCompact` half: already in `Section4/D01/ForceClass.lean`
-- (`memForceCompact_of_smooth_support`), reused, not reproved.
example : ∀ (f : SpaceTimeField), ContDiff ℝ ∞ f → HasCompactSupport f →
    (∀ z ∈ tsupport f, 0 < z.1) → MemForceCompact f :=
  fun _ hs hc hp => NSFormalization.Section4.D01.memForceCompact_of_smooth_support hs hc hp

/-! ## Unit 2: `approxCompact` (`research/B01/Spec.lean:312`) -/

example : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ s : ℝ,
    CompletedDense q s forceClassCompact :=
  NSFormalization.Section4.B01.approxCompact

/-! ## Unit 3: the four `completion*` fields (`research/B01/Spec.lean:320-338`) -/

example : ∀ (q : ℝ≥0∞) (s : ℝ) (u : bochnerSpace q s),
    MemBochnerDatum q s (u : ℝ → RealVectorSobolev s) :=
  NSFormalization.Section4.B01.completionRepresentative

example : ∀ (q : ℝ≥0∞) (s : ℝ) (b : ℝ → RealVectorSobolev s),
    MemBochnerDatum q s b →
      ∃ u : bochnerSpace q s, (u : ℝ → RealVectorSobolev s) =ᵐ[forceTimeMeasure] b :=
  NSFormalization.Section4.B01.completionSurjective

example : ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : ℝ) (u : bochnerSpace q s),
    bochnerDatumENorm q s (u : ℝ → RealVectorSobolev s) = ‖u‖ₑ :=
  NSFormalization.Section4.B01.completionNorm

example : ∀ (q : ℝ≥0∞) (s : ℝ) (b c : ℝ → RealVectorSobolev s),
    b =ᵐ[forceTimeMeasure] c → bochnerDatumENorm q s b = bochnerDatumENorm q s c :=
  NSFormalization.Section4.B01.completionCongr

/-! ## Axiom audit -/

#print axioms NSFormalization.Section4.B01.isSobolevPath_angularRealVectorSlice
#print axioms NSFormalization.Section4.B01.aestronglyMeasurable_angularRealVectorSlice
#print axioms NSFormalization.Section4.B01.bochnerDatumENorm_toLp_sub
#print axioms NSFormalization.Section4.B01.approxCompact
#print axioms NSFormalization.Section4.B01.completionRepresentative
#print axioms NSFormalization.Section4.B01.completionSurjective
#print axioms NSFormalization.Section4.B01.completionNorm
#print axioms NSFormalization.Section4.B01.completionCongr

end
