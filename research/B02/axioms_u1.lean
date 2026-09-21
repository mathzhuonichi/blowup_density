/-
Conformance check for B02 unit 1 (`annular_truncation`).

`research/B02/Spec.lean` is a standalone file (namespace `BlowupDensity.B02.Draft`)
that is not on the Lake module path, so it cannot be imported.  This file instead
re-states the five relevant `def`s of `Spec.lean:155-192`
(`frequencyAnnulus`, `closedFrequencyAnnulus`, `IsAnnularDatum`,
`IsAnnularRestriction`, `IsAnnularSupported`) **verbatim** in the namespace
`BlowupDensity.B02.SpecMirror`, and then exhibits `example`s whose types are the
two spec fields `annularRestriction` and `annularSmoothing`
(`Spec.lean:302-318`), each discharged by the theorem proved in
`NSFormalization/Section4/B02/Annular.lean`.

The `example`s type-check because the mirrored `SpecMirror.*` predicates and the
`NSFormalization.Section4.B02.*` predicates used inside the theorems are the same
term (token-for-token copies), hence definitionally equal.

Check with:
  cd verification && lake env lean ../research/B02/axioms_u1.lean
-/
import NSFormalization.Section4.B02.Annular

noncomputable section

open MeasureTheory Set
open NSFormalization.Paper3 (RealVectorSobolev)
open NSFormalization.Source.RealSobolev (FourierData)
open NavierStokes.ProblemStatement (Space)
open scoped ENNReal ContDiff

namespace BlowupDensity.B02.SpecMirror

/-- Verbatim `research/B02/Spec.lean:155`. -/
def frequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ < ‖ξ‖ ∧ ‖ξ‖ < R}

/-- Verbatim `research/B02/Spec.lean:161`. -/
def closedFrequencyAnnulus (δ R : ℝ) : Set Space := {ξ : Space | δ ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R}

/-- Verbatim `research/B02/Spec.lean:172`. -/
def IsAnnularDatum {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∃ g : Fin 3 → Space → ℂ,
    (∀ i, ContDiff ℝ ∞ (g i)) ∧
    (∀ i, tsupport (g i) ⊆ closedFrequencyAnnulus δ R) ∧
    (∀ i, ((Z i : FourierData) : Space → ℂ) =ᵐ[volume] g i)

/-- Verbatim `research/B02/Spec.lean:181`. -/
def IsAnnularRestriction {s : ℝ} (δ R : ℝ) (A Z : RealVectorSobolev s) : Prop :=
  ∀ i, ((Z i : FourierData) : Space → ℂ)
    =ᵐ[volume] (frequencyAnnulus δ R).indicator ((A i : FourierData) : Space → ℂ)

/-- Verbatim `research/B02/Spec.lean:190`. -/
def IsAnnularSupported {s : ℝ} (δ R : ℝ) (Z : RealVectorSobolev s) : Prop :=
  ∀ i : Fin 3, ∀ᵐ ξ : Space ∂volume,
    ξ ∉ frequencyAnnulus δ R → ((Z i : FourierData) : Space → ℂ) ξ = 0

/-- The type of `HomogeneousApproxAPI.annularRestriction`, `research/B02/Spec.lean:302-304`,
discharged by `NSFormalization.Section4.B02.annularRestriction`. -/
example : ∀ (s : ℝ) (A : RealVectorSobolev s) (η : ℝ≥0∞), 0 < η →
    ∃ (δ R : ℝ) (Z : RealVectorSobolev s),
      0 < δ ∧ δ < R ∧ IsAnnularRestriction δ R A Z ∧ ‖Z - A‖ₑ < η :=
  NSFormalization.Section4.B02.annularRestriction

/-- The type of `HomogeneousApproxAPI.annularSmoothing`, `research/B02/Spec.lean:314-318`,
discharged by `NSFormalization.Section4.B02.annularSmoothing`. -/
example : ∀ (s : ℝ) (δ R : ℝ), 0 < δ → δ < R →
      ∀ (Z : RealVectorSobolev s), IsAnnularSupported δ R Z →
      ∀ η : ℝ≥0∞, 0 < η →
    ∃ (δ' R' : ℝ) (W : RealVectorSobolev s),
      0 < δ' ∧ δ' < δ ∧ R < R' ∧ IsAnnularDatum δ' R' W ∧ ‖W - Z‖ₑ < η :=
  NSFormalization.Section4.B02.annularSmoothing

end BlowupDensity.B02.SpecMirror

#print axioms NSFormalization.Section4.B02.annularRestriction
#print axioms NSFormalization.Section4.B02.annularSmoothing
