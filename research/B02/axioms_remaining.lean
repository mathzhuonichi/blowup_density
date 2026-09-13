import Contracts.V1.Data
import NSFormalization.Section4.B02.Remaining

/-!
# B02 remaining-fields conformance (lane 097)

`example` blocks whose types are the `S`-size fields of `research/B02/Spec.lean`'s
`HomogeneousApproxAPI` that lane 097 discharges, each inhabited by the theorems of
`NSFormalization.Section4.B02.Remaining`, followed by `#print axioms` for every
public declaration.  Checked with
`cd verification && lake env lean ../research/B02/axioms_remaining.lean`.

Two shapes of `example`.

* The four `χ` fields (`chi_smooth`, `chi_one`, `chi_vanishes`, `chi_range`,
  `Spec.lean:279-288`) mention only `Space`, `‖·‖`, `Icc` and the chosen `χ`; the
  examples state them on `χ := NavierStokesR3.ComparisonCutoffs.baseCutoff`, the
  same object the `B01` binding uses (`Bindings/BochnerPartial.lean:66`).
* `temporalApprox` (`Spec.lean:563`) is transcribed from `Spec.lean` in the
  namespace it uses (`open BlowupDensity.Contracts.V1.Data`,
  `NavierStokes.ProblemStatement (Space)`,
  `NSFormalization.Paper3 (RealVectorSobolev)`), with the spec-local `separatedPath`
  (`Spec.lean:219`) restated verbatim, exactly as `research/B01/axioms_u7.lean`.
  It typechecks because each restated predicate in
  `Section4/B01/{Compact,Separated}.lean` is definitionally equal to its
  `Contracts.V1.Data` counterpart, and the two `separatedPath` `def`s are equal.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

/-! ## The fixed spatial cutoff `χ` (`research/B02/Spec.lean:279-288`) -/

-- `chi_smooth` (`Spec.lean:280`), with `χ := baseCutoff`.
example : ContDiff ℝ ∞ (NavierStokesR3.ComparisonCutoffs.baseCutoff : Space → ℝ) :=
  NSFormalization.Section4.B02.chi_smooth

-- `chi_one` (`Spec.lean:282`).
example : ∀ x : Space, ‖x‖ ≤ 1 → NavierStokesR3.ComparisonCutoffs.baseCutoff x = 1 :=
  NSFormalization.Section4.B02.chi_one

-- `chi_vanishes` (`Spec.lean:285`).
example : ∀ x : Space, 2 ≤ ‖x‖ → NavierStokesR3.ComparisonCutoffs.baseCutoff x = 0 :=
  NSFormalization.Section4.B02.chi_vanishes

-- `chi_range` (`Spec.lean:287`).
example : ∀ x : Space, NavierStokesR3.ComparisonCutoffs.baseCutoff x ∈ Icc (0 : ℝ) 1 :=
  NSFormalization.Section4.B02.chi_range

/-! ## The Bochner temporal stage `temporalApprox` (`research/B02/Spec.lean:563`) -/

/-- `research/B02/Spec.lean:219`, restated verbatim: the order-`s` datum path of a
finite separated sum.  The same `def` as `research/B01/Spec.lean:147`. -/
def separatedPath {J : ℕ} {s : ℝ} (φ : Fin J → ℝ → ℝ)
    (A : Fin J → RealVectorSobolev s) : ℝ → RealVectorSobolev s :=
  fun t => ∑ j, φ j t • A j

-- `temporalApprox` (`Spec.lean:563`): the spec field type verbatim, in the
-- `Contracts.V1.Data` vocabulary, inhabited by the `B02` reuse theorem.
example : ∀ (q : ℝ≥0∞), 1 ≤ q → q ≠ ⊤ → ∀ (s : ℝ)
    (b : ℝ → RealVectorSobolev s), MemBochnerDatum q s b → ∀ η : ℝ≥0∞, 0 < η →
    ∃ (J : ℕ) (φ : Fin J → ℝ → ℝ) (A : Fin J → RealVectorSobolev s),
      (∀ j, ContDiff ℝ ∞ (φ j)) ∧ (∀ j, HasCompactSupport (φ j)) ∧
      (∀ j, tsupport (φ j) ⊆ Ioi (0 : ℝ)) ∧
      bochnerDatumENorm q s (separatedPath φ A - b) < η :=
  NSFormalization.Section4.B02.temporalApprox

/-! ## Axiom audit — every public declaration is exactly `[propext, Classical.choice, Quot.sound]` -/

#print axioms NSFormalization.Section4.B02.chi_smooth
#print axioms NSFormalization.Section4.B02.chi_one
#print axioms NSFormalization.Section4.B02.chi_vanishes
#print axioms NSFormalization.Section4.B02.chi_range
#print axioms NSFormalization.Section4.B02.temporalApprox

end
