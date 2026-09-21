import NSFormalization.Section4.B01.Compact

/-!
# B01 unit 3: identification of the datum-path model with the bundled Bochner space

Unit 3 (`research/B01/COMPARISON.md:147`), `completion_identification`: the four `completion*`
fields of `research/B01/Spec.lean:320-338`, which record that the datum-path model
`Data.MemBochnerDatum` and the bundled Bochner space `bochnerSpace q s = L^q(0,∞;H^s(R³;R³))`
are the same object.  All four are immediate from Mathlib's `Lp`/`MemLp` API:

* `completionRepresentative` — `Lp.memLp`;
* `completionSurjective` — `MemLp.toLp`/`MemLp.coeFn_toLp`;
* `completionNorm` — `Lp.enorm_def`;
* `completionCongr` — `eLpNorm_congr_ae`.

The restated vocabulary (`MemBochnerDatum`, `bochnerDatumENorm`, `bochnerSpace`,
`forceTimeMeasure`) is inherited from `Section4/B01/Compact.lean` and `Section4/D01/ForceClass.lean`.
-/

noncomputable section

namespace NSFormalization.Section4.B01

open Set MeasureTheory NavierStokes.ProblemStatement
open NSFormalization.Paper3
open NSFormalization.Section4.D01
open scoped ContDiff ENNReal SchwartzMap

/-- **`completionRepresentative`** (`research/B01/Spec.lean:320`).  Every element of the bundled
Bochner space `L^q(0,∞;H^s(R³;R³))` is a datum path in the sense of `Data.MemBochnerDatum`. -/
theorem completionRepresentative (q : ℝ≥0∞) (s : ℝ) (u : bochnerSpace q s) :
    MemBochnerDatum q s (u : ℝ → RealVectorSobolev s) :=
  Lp.memLp u

/-- **`completionSurjective`** (`research/B01/Spec.lean:325`).  Conversely every datum path is
represented (a.e.) by an element of the bundled space, so quantifying `approxCompact` over paths
misses no element of the completion. -/
theorem completionSurjective (q : ℝ≥0∞) (s : ℝ) (b : ℝ → RealVectorSobolev s)
    (hb : MemBochnerDatum q s b) :
    ∃ u : bochnerSpace q s, (u : ℝ → RealVectorSobolev s) =ᵐ[forceTimeMeasure] b := by
  have hb' : MemLp b q forceTimeMeasure := hb
  exact ⟨hb'.toLp b, hb'.coeFn_toLp⟩

/-- **`completionNorm`** (`research/B01/Spec.lean:331`).  `Data.bochnerDatumENorm` on a
representative is the Banach norm of the class. -/
theorem completionNorm (q : ℝ≥0∞) [Fact (1 ≤ q)] (s : ℝ) (u : bochnerSpace q s) :
    bochnerDatumENorm q s (u : ℝ → RealVectorSobolev s) = ‖u‖ₑ := by
  show eLpNorm (u : ℝ → RealVectorSobolev s) q forceTimeMeasure = ‖u‖ₑ
  rw [Lp.enorm_def]

/-- **`completionCongr`** (`research/B01/Spec.lean:337`).  `Data.bochnerDatumENorm` only sees the
a.e. class, the "identified almost everywhere" convention of `01-introduction.tex:124`. -/
theorem completionCongr (q : ℝ≥0∞) (s : ℝ) (b c : ℝ → RealVectorSobolev s)
    (h : b =ᵐ[forceTimeMeasure] c) :
    bochnerDatumENorm q s b = bochnerDatumENorm q s c :=
  eLpNorm_congr_ae h

end NSFormalization.Section4.B01
