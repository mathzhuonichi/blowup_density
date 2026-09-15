import Contracts.V1.HomogeneousPartial
import NSFormalization.Section4.B02.LowFrequency
import NSFormalization.Section4.B02.Annular
import NSFormalization.Section4.B02.LowHigh
import NSFormalization.Section4.B02.Cutoff
import NSFormalization.Section4.B02.LebesgueDatum
import NSFormalization.Section4.B02.AnnularReal
import NSFormalization.Section4.B02.Remaining
import NavierStokes.R3.ComparisonCutoffs

/-! The only layer that knows the current implementation's names and paths for the
proved part of the homogeneous `L²(0,∞;Ḣ^{-1}(R³))` approximation of Proposition 4.6.

`Contracts.V1.HomogeneousPartial` is self-contained — its only imports are two
other contracts, `Contracts.V1.Data` and `Contracts.V1.BochnerPartial` — so this
adapter has two jobs: record by `rfl` that each spec-local object the specification
restates is the notion the eight `Section4/B02` modules use, and assemble the
proved theorems into the contract.

The 16 proved fields are the theorems of
`NSFormalization.Section4.B02.{LowFrequency,Annular,LowHigh,Cutoff,LebesgueDatum,
AnnularReal,Remaining}` verbatim (defeq bridges the contract's `Data`/`BochnerPartial`
vocabulary to the modules' token-for-token restatements, exactly as the conformance
files `research/B02/axioms_{u1,u2_sl3,u34,u6,u7,u8,remaining}.lean` check):

* `chi_smooth … chi_range` — the same-named `Remaining.lean` theorems, on the vendor
  cutoff `NavierStokesR3.ComparisonCutoffs.baseCutoff`, the **same** object the
  `B01` binding uses (`Bindings/BochnerPartial.lean:66`), so a joint consumer sees
  one cutoff across `B01` and `B02`.
* `annularRestriction`, `annularSmoothing`, `annularSchwartz`,
  `lowFrequencyIntegrable`, `lowFrequencyIntegral`, `fourierSupBound`,
  `cutoffLebesgue`, `spatialApproxHomogeneous`, `temporalApprox` — the same-named
  theorems, assigned directly.
* `lowHighSplit`, `lebesgueHomogeneousDatum` — the same-named theorems, whose
  `-3/2 < s` and `s ≤ 0` hypotheses are supplied from the packed `SplitRange s`.
* `homogeneousDatumSub` — `isHomogeneousSliceDatum_sub_of_integrable`, the
  integrability-carrying form (the hypothesis-free form is false; see the ⚠ note in
  the contract docstring).

Every declaration here carries a `homogeneousPartial_` prefix;
`BlowupDensity.Bindings` is a flat namespace shared by all adapters. -/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal SchwartzMap

section Correspondence

variable {s : ℝ} (δ R : ℝ) (A Z : RealVectorSobolev s) (χ : Space → ℝ)
  (ψ : Fin 3 → SchwartzMap Space ℝ)

/-- The contract's open frequency annulus is the implementation's. -/
theorem homogeneousPartial_frequencyAnnulus_eq :
    Contracts.V1.HomogeneousPartial.frequencyAnnulus δ R
      = NSFormalization.Section4.B02.frequencyAnnulus δ R := rfl

/-- The contract's closed frequency annulus is the implementation's. -/
theorem homogeneousPartial_closedFrequencyAnnulus_eq :
    Contracts.V1.HomogeneousPartial.closedFrequencyAnnulus δ R
      = NSFormalization.Section4.B02.closedFrequencyAnnulus δ R := rfl

/-- The contract's annular datum predicate is the implementation's. -/
theorem homogeneousPartial_isAnnularDatum_eq :
    Contracts.V1.HomogeneousPartial.IsAnnularDatum δ R Z
      = NSFormalization.Section4.B02.IsAnnularDatum δ R Z := rfl

/-- The contract's annular restriction predicate is the implementation's. -/
theorem homogeneousPartial_isAnnularRestriction_eq :
    Contracts.V1.HomogeneousPartial.IsAnnularRestriction δ R A Z
      = NSFormalization.Section4.B02.IsAnnularRestriction δ R A Z := rfl

/-- The contract's annular support predicate is the implementation's. -/
theorem homogeneousPartial_isAnnularSupported_eq :
    Contracts.V1.HomogeneousPartial.IsAnnularSupported δ R Z
      = NSFormalization.Section4.B02.IsAnnularSupported δ R Z := rfl

/-- The contract's dilated cutoff is the implementation's. -/
theorem homogeneousPartial_scaledCutoff_eq :
    Contracts.V1.HomogeneousPartial.scaledCutoff χ R
      = NSFormalization.Section4.B02.scaledCutoff χ R := rfl

/-- The contract's Schwartz vector field is the implementation's. -/
theorem homogeneousPartial_schwartzVector_eq :
    Contracts.V1.HomogeneousPartial.schwartzVector ψ
      = NSFormalization.Section4.B02.schwartzVector ψ := rfl

/-- The contract's low/high constant is the implementation's. -/
theorem homogeneousPartial_lowHighConstant_eq (s : ℝ) :
    Contracts.V1.HomogeneousPartial.lowHighConstant s
      = NSFormalization.Section4.B02.lowHighConstant s := rfl

/-- The contract's split range is the implementation's. -/
theorem homogeneousPartial_splitRange_eq (s : ℝ) :
    Contracts.V1.HomogeneousPartial.SplitRange s
      = NSFormalization.Section4.B02.SplitRange s := rfl

end Correspondence

/-- Bind the proved fields of the homogeneous `Ḣ^{-1}` approximation to the stable
version-one contract. -/
def homogeneousPartial : Contracts.V1.HomogeneousPartial.HomogeneousApproxPartialAPI where
  χ := NavierStokesR3.ComparisonCutoffs.baseCutoff
  chi_smooth := NSFormalization.Section4.B02.chi_smooth
  chi_one := NSFormalization.Section4.B02.chi_one
  chi_vanishes := NSFormalization.Section4.B02.chi_vanishes
  chi_range := NSFormalization.Section4.B02.chi_range
  annularRestriction := NSFormalization.Section4.B02.annularRestriction
  annularSmoothing := NSFormalization.Section4.B02.annularSmoothing
  annularSchwartz := NSFormalization.Section4.B02.annularSchwartz
  lowFrequencyIntegrable := NSFormalization.Section4.B02.lowFrequencyIntegrable
  lowFrequencyIntegral := NSFormalization.Section4.B02.lowFrequencyIntegral
  fourierSupBound := NSFormalization.Section4.B02.fourierSupBound
  lowHighSplit := fun s hs k hk1 hk2 =>
    NSFormalization.Section4.B02.lowHighSplit s hs.1 hs.2 k hk1 hk2
  lebesgueHomogeneousDatum := fun _s hs k hk1 hk2 =>
    NSFormalization.Section4.B02.lebesgueHomogeneousDatum hs.1 hs.2 k hk1 hk2
  homogeneousDatumSub := fun _s _z _w _Z _W hZ hW hz hw =>
    NSFormalization.Section4.B02.isHomogeneousSliceDatum_sub_of_integrable hZ hW hz hw
  cutoffLebesgue := NSFormalization.Section4.B02.cutoffLebesgue
  spatialApproxHomogeneous := NSFormalization.Section4.B02.spatialApproxHomogeneous
  temporalApprox := NSFormalization.Section4.B02.temporalApprox

end BlowupDensity.Bindings
