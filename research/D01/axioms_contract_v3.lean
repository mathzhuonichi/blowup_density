import Contracts.V3.DatumLemmas
import Bindings.DatumLemmasV3

/-!
# Conformance: P2 (eq:Rpressure) as the version-3 datum-lemmas contract

Checks that `Bindings.datumLemmasV3` inhabits `Contracts.V3.DatumLemmas.DatumLemmasV3API`
with only the standard logical axioms, that the version-2 projection is the frozen
version-2 witness (`rfl`), that the two restated slice operators are the pinned
upstream ones (`rfl`), and that each of the three P2 fields, read out of the
witness, still uses only the standard axioms.

Run: `cd verification && lake env lean ../research/D01/axioms_contract_v3.lean`
Expected: every `#print axioms` prints exactly `[propext, Classical.choice, Quot.sound]`.
-/

namespace BlowupDensity.Bindings

open Set
open BlowupDensity.Contracts.V1
open BlowupDensity.Contracts.V1.Data
open NSFormalization.Paper3 (RealVectorSobolev)

/-! ## `rfl` bridges: the V3 fields are stated with the pinned upstream operators -/

example : @NavierStokes.ProblemStatement.pressureGradient
    = @BlowupDensity.Contracts.V1.pressureGradient := rfl
example : @NavierStokes.ProblemStatement.temporalDerivative
    = @BlowupDensity.Contracts.V1.temporalDerivative := rfl

/-! ## The version-2 projection is the frozen version-2 witness -/

example : datumLemmasV3.toDatumLemmasV2API = datumLemmasV2 := rfl

/-! ## The three P2 fields, read from the witness, in the manuscript's shape -/

example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => pressureGradient u.pressure t x :=
  datumLemmasV3.solution_slice_pressureGradient_smoothJets

example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      SmoothSquareIntegrableJets fun x : Space => temporalDerivative u.velocity t x :=
  datumLemmasV3.solution_slice_temporalDerivative_smoothJets

example :
    ∀ (ν : ℝ) (a : SpatialField) (f : SpaceTimeField) (T : ℝ)
      (u : ClassicalSolutionR ν a f T), MemForceR f → ∀ t : ℝ, t ∈ Ioo (0 : ℝ) T →
      ∀ m : ℕ, ∃ P : RealVectorSobolev (m : ℝ),
        IsSobolevDatum (m : ℝ) (fun x : Space => pressureGradient u.pressure t x) P :=
  datumLemmasV3.solution_slice_pressureGradient_exists_datum

#print axioms datumLemmasV3
#print axioms NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR
#print axioms NSFormalization.Section4.D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR
#print axioms NSFormalization.Section4.D01.exists_isSobolevDatum_pressureGradient_slice

end BlowupDensity.Bindings
