/-
Conformance check for B02 unit 8 (`cutoff_lebesgue` + `spatial_dense`).

`research/B02/Spec.lean` is a standalone file (namespace `BlowupDensity.B02.Draft`)
not on the Lake module path, so it cannot be imported.  This file instead:

* re-states the Spec-only `def`s used by unit 8 — `scaledCutoff`, `schwartzVector`,
  `SplitRange`, `lowHighConstant`, and (for `annularSchwartz`) `closedFrequencyAnnulus`
  / `IsAnnularDatum` — **verbatim** from `research/B02/Spec.lean` in the namespace
  `BlowupDensity.B02.SpecMirror`, using the frozen `Contracts.V1.Data` objects
  `SpatialField`, `IsHomogeneousSliceDatum`, `homogeneousFourierENorm`;
* exhibits an `example` whose type is the spec field `cutoffLebesgue`
  (`Spec.lean:489-497`, with `χ := baseCutoff`), discharged by
  `NSFormalization.Section4.B02.cutoffLebesgue`;
* exhibits an `example` whose type is the arrow
  `annularSchwartz → lebesgueHomogeneousDatum → homogeneousDatumSub → lowHighSplit
   → spatialApproxHomogeneous` — i.e. the four hypotheses of
  `spatialApproxHomogeneous_of` are **exactly** the spec fields of units 2/6/7
  (`Spec.lean:362-364, 454-458, 470-472, 421-425`), token-for-token, and the
  conclusion is the spec field `spatialApproxHomogeneous` (`Spec.lean:515-518`),
  discharged by `NSFormalization.Section4.B02.spatialApproxHomogeneous_of`.

The `example`s type-check because the mirrored `SpecMirror.*` predicates and the
`NSFormalization.Section4.B02.*` / `Contracts.V1.Data.*` predicates used inside the
theorems are token-for-token copies, hence definitionally equal.

Check with:
  cd verification && lake env lean ../research/B02/axioms_u8.lean
-/
import Contracts.V1.Data
import NSFormalization.Section4.B02.Cutoff

noncomputable section

open MeasureTheory Set Filter
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData)
open NavierStokes.ProblemStatement (Space)
open NavierStokesR3.ComparisonCutoffs (baseCutoff)
open BlowupDensity.Contracts.V1.Data
open scoped ENNReal ContDiff SchwartzMap

namespace BlowupDensity.B02.SpecMirror

/-- Verbatim `research/B02/Spec.lean:161`. -/
def closedFrequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R}

/-- Verbatim `research/B02/Spec.lean:172`. -/
def IsAnnularDatum {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∃ g : Fin 3 → Space → ℂ,
    (∀ i, ContDiff ℝ ∞ (g i)) ∧
    (∀ i, tsupport (g i) ⊆ closedFrequencyAnnulus δ R) ∧
    (∀ i, ((Z i : FourierData) : Space → ℂ) =ᵐ[volume] g i)

/-- Verbatim `research/B02/Spec.lean:199`. -/
def scaledCutoff (χ : Space → ℝ) (R : ℝ) : Space → ℝ := fun x => χ (R⁻¹ • x)

/-- Verbatim `research/B02/Spec.lean:206`. -/
def schwartzVector (ψ : Fin 3 → SchwartzMap Space ℝ) : SpatialField :=
  fun x => WithLp.toLp 2 (fun i => ψ i x)

/-- Verbatim `research/B02/Spec.lean:231`. -/
def lowHighConstant (s : ℝ) : ℝ :=
  (2 * Real.pi) ^ (-(3 : ℝ)) * ∫ ξ in Metric.ball (0 : Space) 1, ‖ξ‖ ^ (2 * s)

/-- Verbatim `research/B02/Spec.lean:237`. -/
def SplitRange (s : ℝ) : Prop := -3 / 2 < s ∧ s ≤ 0

/-- The type of `HomogeneousApproxAPI.cutoffLebesgue`, `research/B02/Spec.lean:489-497`
(with `χ := baseCutoff`), discharged by `NSFormalization.Section4.B02.cutoffLebesgue`. -/
example : ∀ ψ : Fin 3 → SchwartzMap Space ℝ,
    Filter.Tendsto
      (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff baseCutoff R x) • schwartzVector ψ x) 1 volume)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto
      (fun R : ℝ =>
        eLpNorm (fun x => (1 - scaledCutoff baseCutoff R x) • schwartzVector ψ x) 2 volume)
      Filter.atTop (nhds 0) :=
  NSFormalization.Section4.B02.cutoffLebesgue

/-- The four antecedents are the spec fields `annularSchwartz` (`Spec.lean:362-364`),
`lebesgueHomogeneousDatum` (`Spec.lean:454-458`), `homogeneousDatumSub`
(`Spec.lean:470-472`) and `lowHighSplit` (`Spec.lean:421-425`), verbatim; the
consequent is the spec field `spatialApproxHomogeneous` (`Spec.lean:515-518`).
Discharged by `NSFormalization.Section4.B02.spatialApproxHomogeneous_of`. -/
example :
    (∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
        ∀ W : RealVectorSobolev s, IsAnnularDatum δ R W →
      ∃ ψ : Fin 3 → SchwartzMap Space ℝ, IsHomogeneousSliceDatum s (schwartzVector ψ) W) →
    (∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
        MemLp k 1 volume → MemLp k 2 volume →
      (∃ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G) ∧
        ∀ G : RealVectorSobolev s, IsHomogeneousSliceDatum s k G →
          ‖G‖ₑ = homogeneousFourierENorm s k) →
    (∀ (s : ℝ) (z w : SpatialField) (Z W : RealVectorSobolev s),
        IsHomogeneousSliceDatum s z Z → IsHomogeneousSliceDatum s w W →
          IsHomogeneousSliceDatum s (z - w) (Z - W)) →
    (∀ s : ℝ, SplitRange s → ∀ k : SpatialField,
        MemLp k 1 volume → MemLp k 2 volume →
      homogeneousFourierENorm s k ^ (2 : ℝ) ≤
        ENNReal.ofReal (lowHighConstant s) * eLpNorm k 1 volume ^ (2 : ℝ) +
          eLpNorm k 2 volume ^ (2 : ℝ)) →
    ∀ s : ℝ, SplitRange s → ∀ (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
      ∃ (h : SpatialField) (H : RealVectorSobolev s),
        ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ IsHomogeneousSliceDatum s h H ∧ ‖H - A‖ₑ < η :=
  NSFormalization.Section4.B02.spatialApproxHomogeneous_of

end BlowupDensity.B02.SpecMirror

#print axioms NSFormalization.Section4.B02.cutoffLebesgue
#print axioms NSFormalization.Section4.B02.spatialApproxHomogeneous_of
