import Contracts.V3.DatumLemmas
import Bindings.DatumLemmasV2
import Bindings.Uniqueness
import NSFormalization.Section4.D01.PressureJets

/-! The implementation layer for the version-three datum-lemmas contract.

`Contracts.V3.DatumLemmas.DatumLemmasV3API` extends
`Contracts.V2.DatumLemmas.DatumLemmasV2API` by the three P2 fields
(`eq:Rpressure`, `02-preliminaries.tex:89-94`), all proved in
`NSFormalization.Section4.D01.PressureJets` (lane 117,
`research/D01/REVIEW_SL8_ASSEMBLY.md`).  This file has three jobs.

* `datumLemmasV3` inhabits the version-three record.  It reuses the frozen
  version-two witness `Bindings.datumLemmasV2` with `{ … with … }` and fills the
  three new fields with the `PressureJets.lean` theorems directly — no `by`
  block, only the field-by-field structure conversion `uniqueness_toA02` from
  `Contracts.V1.Data.ClassicalSolutionR` to `Section4.A02.ClassicalSolutionR`
  (the two are different inductive types, `CLAUDE.md`'s structure exception, so
  no `rfl` bridge is possible; `(uniqueness_toA02 u).pressure = u.pressure` and
  `.velocity = u.velocity` are `rfl`, `Bindings/Uniqueness.lean:79,83`).
* `datumLemmasV3_toDatumLemmasV2API_eq` records that version two is recovered from
  version three by the inherited projection; the recovery is definitional, so it
  cannot drift, and `Tests.checkedDatumLemmasV2` keeps using the untouched
  `Bindings.datumLemmasV2`.
* §1's `rfl` bridges pin `Contracts.V1.Packet`'s `pressureGradient` and
  `temporalDerivative` — the operators the V3 fields are stated with — to the
  pinned upstream `NavierStokes.ProblemStatement` ones the `PressureJets.lean`
  theorems conclude in, so CI fails if either side drifts.  The remaining notions
  need no new bridge: `Section4.D01.SmoothSquareIntegrableJets =
  Contracts.V1.SmoothSquareIntegrableJets` and `A02.MemForceR =
  Contracts.V1.Data.MemForceR` are already pinned in `Bindings.DatumLemmas`
  (`datumLemmas_smoothSquareIntegrableJets_eq`, `datumLemmas_memForceR_eq`),
  imported here through `Bindings.DatumLemmasV2`; `IsSobolevDatum` and
  `RealVectorSobolev` are `Contracts.V1.Data`'s and `NSFormalization.Paper3`'s own,
  used on both sides.
-/

noncomputable section
namespace BlowupDensity.Bindings

/-! ## 1. Correspondence: the restated slice operators are the contract's own -/

section Correspondence

/-- `Contracts.V1.Packet`'s `pressureGradient` (`Packet.lean:115`) is the pinned
upstream `NavierStokes.ProblemStatement.pressureGradient`
(`vendor/NavierStokesAndEuler/NavierStokes/ProblemStatement.lean:71`), the
`∑ᵢ (∂ᵢp)eᵢ` the V3 fields are stated with.  Same `rfl` the lane-117 reviewer
recorded (`research/D01/REVIEW_SL8_ASSEMBLY.md` appendix D). -/
theorem datumLemmasV3_pressureGradient_eq :
    @NavierStokes.ProblemStatement.pressureGradient
      = @BlowupDensity.Contracts.V1.pressureGradient := rfl

/-- `Contracts.V1.Packet`'s `temporalDerivative` (`Packet.lean:99`) is the pinned
upstream `NavierStokes.ProblemStatement.temporalDerivative`
(`ProblemStatement.lean:55`), the `∂ₜu` the corollary field is stated with. -/
theorem datumLemmasV3_temporalDerivative_eq :
    @NavierStokes.ProblemStatement.temporalDerivative
      = @BlowupDensity.Contracts.V1.temporalDerivative := rfl

end Correspondence

/-! ## 2. The contract -/

/-- Bind the P2 theorems of lane 117 to the stable version-three contract, on top
of the frozen version-two witness.

The three new fields are `Section4/D01/PressureJets.lean`'s theorems verbatim,
applied to the A02 solution `uniqueness_toA02 u`.  The conclusions match the
contract fields definitionally: `(uniqueness_toA02 u).pressure` and `.velocity`
reduce to `u.pressure` / `u.velocity` (`Bindings/Uniqueness.lean:79,83`), the two
`pressureGradient` / `temporalDerivative` operators coincide (§1), and
`Section4.D01.SmoothSquareIntegrableJets` is `Contracts.V1.SmoothSquareIntegrableJets`
(`Bindings.DatumLemmas`). -/
def datumLemmasV3 : Contracts.V3.DatumLemmas.DatumLemmasV3API :=
  { Bindings.datumLemmasV2 with
    solution_slice_pressureGradient_smoothJets := fun _ _ _ _ u hf _ ht =>
      NSFormalization.Section4.D01.pressureGradient_slice_smoothSquareIntegrableJets_of_memForceR
        (uniqueness_toA02 u) hf ht
    solution_slice_temporalDerivative_smoothJets := fun _ _ _ _ u hf _ ht =>
      NSFormalization.Section4.D01.temporalDerivative_slice_smoothSquareIntegrableJets_of_memForceR
        (uniqueness_toA02 u) hf ht
    solution_slice_pressureGradient_exists_datum := fun _ _ _ _ u hf _ ht m =>
      NSFormalization.Section4.D01.exists_isSobolevDatum_pressureGradient_slice
        (uniqueness_toA02 u) hf ht m }

/-- The version-two projection of the version-three witness is the frozen
version-two witness itself.  `{ datumLemmasV2 with … }` fills the inherited
`toDatumLemmasV2API` with `datumLemmasV2` unchanged, so the projection is
definitional.  What this rules out is a version three that quietly drops or
weakens a version-two (hence version-one) field, which would make the projection
fail to typecheck. -/
theorem datumLemmasV3_toDatumLemmasV2API_eq :
    datumLemmasV3.toDatumLemmasV2API = Bindings.datumLemmasV2 := rfl

end BlowupDensity.Bindings
