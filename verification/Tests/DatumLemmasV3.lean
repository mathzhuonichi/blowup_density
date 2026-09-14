import Contracts.V3.DatumLemmas
import Bindings.DatumLemmasV3
import TestSupport.Axioms

/-! The exact public type and its transitive trust boundary are both checked.

The version-one and version-two tests `Tests.DatumLemmas` / `Tests.DatumLemmasV2`
are untouched and keep running against `Bindings.datumLemmas` /
`Bindings.datumLemmasV2`; this is the third, strongest acceptance test, not a
replacement.  `Bindings.datumLemmasV3_toDatumLemmasV2API_eq` is the checked link:
it projects `Contracts.V2.DatumLemmas.DatumLemmasV2API` out of the version-three
witness, so nothing versions one and two guarantee is lost by version three.

The three `example`s below print the P2 fields in the manuscript's shape
(`eq:Rpressure`, `paper/sections/02-preliminaries.tex:89-94`), each discharged by
the corresponding field of the checked witness, so a drift in a field type is a
compile error here.
-/

noncomputable section
namespace BlowupDensity.Tests

/-- An implementation must supply every field of the unchanged version-one and
version-two specifications **and** the three P2 fields of lane 117
(`Section4/D01/PressureJets.lean`): the pressure-gradient and time-derivative
slices lie in the jet form of `H^∞`, and `∇p(t,·)` has an angular Sobolev datum at
every integer order. -/
def checkedDatumLemmasV3 : Contracts.V3.DatumLemmas.DatumLemmasV3API :=
  Bindings.datumLemmasV3

run_cmd TestSupport.checkAxioms ``checkedDatumLemmasV3

/-! ## The three P2 fields, in the manuscript's shape -/

section Shapes

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)

/-- `eq:Rpressure` regularity: for a classical solution with force in `𝓕_ℝ`, the
pressure-gradient slice `∇p(t,·)` at every interior time lies in `H^∞` (jet form). -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => pressureGradient u.pressure t x :=
  checkedDatumLemmasV3.solution_slice_pressureGradient_smoothJets

/-- The corollary `∂ₜu(t,·) ∈ H^∞` (jet form) on interior slices. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => temporalDerivative u.velocity t x :=
  checkedDatumLemmasV3.solution_slice_temporalDerivative_smoothJets

/-- The `hP` slot of `A04.momentum_datum`: `∇p(t,·)` has an angular Sobolev datum
at every integer order. -/
example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      ∀ m : ℕ, ∃ P : RealVectorSobolev (m : ℝ),
        IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P :=
  checkedDatumLemmasV3.solution_slice_pressureGradient_exists_datum

end Shapes

end BlowupDensity.Tests
