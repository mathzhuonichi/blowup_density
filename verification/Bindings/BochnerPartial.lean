import Contracts.V1.BochnerPartial
import NSFormalization.Section4.B01.Compact
import NSFormalization.Section4.B01.Completion
import NSFormalization.Section4.B01.Separated
import NSFormalization.Section4.B01.Spatial
import NSFormalization.Section4.B01.Temporal
import NSFormalization.Section4.D01.ForceClass
import NavierStokes.R3.ComparisonCutoffs

/-! The only layer that knows the current implementation's names and paths for the
proved part of the compact-force Bochner approximation of Proposition 4.6.

`Contracts.V1.BochnerPartial` is self-contained — its sole import is another
contract, `Contracts.V1.Data` — so this adapter has two jobs: record by `rfl`
that each spec-local object the specification restates is the notion the proof
modules use, and assemble the proved theorems into the contract.

The three spatial/temporal fields (`spatialApprox`, `temporalApprox`,
`approxCompact`) and the four `completion*` fields are the theorems of
`NSFormalization.Section4.B01.{Spatial,Temporal,Compact,Completion}` verbatim
(defeq bridges the contract's `Data` vocabulary to the modules' token-for-token
restatements, exactly as `research/B01/axioms_u123.lean`, `axioms_u68.lean` and
`axioms_u7.lean` check).  `separatedAssembly` is the same theorem with its `J`
made explicit.  `compactSubsetForceR` is `Section4/D01/ForceClass.lean`'s
`memForceR_of_memForceCompact`, pointwise membership repackaged as set
inclusion.  The cutoff `χ` and its four properties are the vendor
`NavierStokesR3.ComparisonCutoffs.baseCutoff` and its estimates.

Every declaration here carries a `bochnerPartial_` prefix; `BlowupDensity.Bindings`
is a flat namespace shared by all adapters. -/

noncomputable section
namespace BlowupDensity.Bindings

open MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open scoped ENNReal

section Correspondence

variable (s : ℝ) {J : ℕ} (φ : Fin J → ℝ → ℝ)
  (h : Fin J → Contracts.V1.Data.SpatialField)
  (A : Fin J → RealVectorSobolev s) (q : ℝ≥0∞)

/-- The contract's separated field is the implementation's. -/
theorem bochnerPartial_separatedField_eq :
    Contracts.V1.BochnerPartial.separatedField φ h
      = NSFormalization.Section4.B01.separatedField φ h := rfl

/-- The contract's separated datum path is the implementation's. -/
theorem bochnerPartial_separatedPath_eq :
    Contracts.V1.BochnerPartial.separatedPath φ A
      = NSFormalization.Section4.B01.separatedPath φ A := rfl

/-- The contract's bundled Bochner space is the implementation's. -/
theorem bochnerPartial_bochnerSpace_eq :
    Contracts.V1.BochnerPartial.bochnerSpace q s
      = NSFormalization.Section4.B01.bochnerSpace q s := rfl

end Correspondence

/-- Bind the proved fields of the compact-force Bochner approximation to the
stable version-one contract. -/
def bochnerPartial : Contracts.V1.BochnerPartial.BochnerPartialAPI where
  χ := NavierStokesR3.ComparisonCutoffs.baseCutoff
  chi_smooth := NavierStokesR3.ComparisonCutoffs.baseCutoff_smooth
  chi_one := fun _ hx => NavierStokesR3.ComparisonCutoffs.baseCutoff_eq_one hx
  chi_vanishes := fun _ hx => NavierStokesR3.ComparisonCutoffs.baseCutoff_eq_zero hx
  chi_range := fun x => ⟨NavierStokesR3.ComparisonCutoffs.baseCutoff_nonneg x,
    NavierStokesR3.ComparisonCutoffs.baseCutoff_le_one x⟩
  spatialApprox := NSFormalization.Section4.B01.spatialApprox
  temporalApprox := NSFormalization.Section4.B01.temporalApprox
  separatedAssembly := fun s _J φ h A hφs hφc hφpos hhs hhc hA =>
    NSFormalization.Section4.B01.separatedAssembly s φ h A hφs hφc hφpos hhs hhc hA
  approxCompact := NSFormalization.Section4.B01.approxCompact
  completionRepresentative := NSFormalization.Section4.B01.completionRepresentative
  completionSurjective := NSFormalization.Section4.B01.completionSurjective
  completionNorm := NSFormalization.Section4.B01.completionNorm
  completionCongr := NSFormalization.Section4.B01.completionCongr
  compactSubsetForceR := fun _ hf =>
    NSFormalization.Section4.D01.memForceR_of_memForceCompact hf

end BlowupDensity.Bindings
