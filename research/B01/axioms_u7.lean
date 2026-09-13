import Contracts.V1.Data
import NSFormalization.Section4.B01.Temporal

/-!
# B01 unit 7 conformance

`example` blocks whose types are the standalone spec `def` `SeparatedTemporalDense`
(`research/B01/Spec.lean:382`) and the `BochnerApproxAPI` field `temporalApprox`
(`research/B01/Spec.lean:273`, unit 7 of `research/B01/COMPARISON.md:151`), each discharged by the
theorems of `NSFormalization.Section4.B01.Temporal`, followed by `#print axioms`.  Checked with
`cd verification && lake env lean ../research/B01/axioms_u7.lean`.

The types below are transcribed from `research/B01/Spec.lean` in the namespace it uses
(`open BlowupDensity.Contracts.V1.Data`, `NavierStokes.ProblemStatement (Space)`,
`NSFormalization.Paper3 (RealVectorSobolev)`), with the Spec-local definition `separatedPath`
(`Spec.lean:147`) restated verbatim.  The examples typecheck because each restated predicate in
`Section4/B01/{Compact,Separated}.lean` is definitionally equal to its `Contracts.V1.Data`
counterpart.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

/-- `research/B01/Spec.lean:147`, restated: the order-`s` datum path of `separatedField φ h`. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

/-! ## The standalone predicate `SeparatedTemporalDense` (`research/B01/Spec.lean:382`) -/

example : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ),
    (∀ (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
      ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
        (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
        (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
        bochnerDatumENorm q s (separatedPath φ A - b) < η) :=
  fun q hq1 hqt s b hb η hη =>
    NSFormalization.Section4.B01.separatedTemporalDense q hq1 hqt s b hb η hη

/-! ## The field `temporalApprox` (`research/B01/Spec.lean:273`) -/

example : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
    (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η :=
  NSFormalization.Section4.B01.temporalApprox

/-! ## Axiom audit -/

#print axioms NSFormalization.Section4.B01.lp_coeFn_finsetSum
#print axioms NSFormalization.Section4.B01.separatedTemporalDense
#print axioms NSFormalization.Section4.B01.temporalApprox

end
