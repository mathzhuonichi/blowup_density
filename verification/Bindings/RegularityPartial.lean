import Contracts.V1.RegularityPartial
import Bindings.Uniqueness
import NSFormalization.Section4.A01.ProjectedEquation
import NSFormalization.Section4.A01.PressureGauge
import NSFormalization.Section4.A01.RadialPotential

/-! The only layer that knows the current implementation's names and paths for the
proved part of the whole-space local-regularity interface of A01.

`Contracts.V1.RegularityPartial` is self-contained — its only import is
`Contracts.V1.Data` — so this adapter has two jobs: record by `rfl` that each
spec-local object the contract restates (and the `Data` object it reuses) is the
notion the proof modules use, and assemble the two proved theorems into the contract.

The two proved fields are the theorems of `Section4/A01/{ProjectedEquation,
PressureGauge}` verbatim, applied to the solution moved across the two
`ClassicalSolutionR` copies by the reused `Bindings.uniqueness_toA02`
(`Contracts.V1.Data.ClassicalSolutionR` and the `Section4/A02` restatement are
distinct inductive types, so a `rfl` bridge for the structure itself is impossible;
each field type is defeq, so the field-wise conversion typechecks — exactly the
mechanism `verification/Bindings/EnergyAbsorptionPartial.lean` uses for `velocityJets`):

* `projected` — `projected_of_classicalSolution` (lane 093).  Its conclusion's
  `convectionDivergence` is drift-guarded by `regularityPartial_convectionDivergence_eq`.
* `pressure_potential` — `pressure_potential_of_classicalSolution` (lane 106).  Its
  conclusion's `pressurePotential` is drift-guarded by
  `regularityPartial_pressurePotential_eq` (the bridge `research/A01/REVIEW_M4.md`
  finding 6 flagged as the load-bearing debt), and its `PressureGaugeEquivOn` by the
  already-registered `Bindings.uniqueness_pressureGaugeEquivOn_eq`
  (`Bindings/Uniqueness.lean`).

`HasSymmetricJacobian` is not referenced by either field; its `rfl` bridge is
recorded here anyway (`regularityPartial_hasSymmetricJacobian_eq`) because the
contract reserves the predicate for the excluded `pressure_recovery` field, whose
`IsLerayComplement` (`Spec.lean:135`) uses it (`RadialPotential.HasSymmetricJacobian`
mirrors a draft spec, not a contract, so it is not itself a CLAUDE.md bridge debt).

Every declaration carries a `regularityPartial_` prefix; `BlowupDensity.Bindings`
is a flat namespace shared by all adapters. -/

noncomputable section
namespace BlowupDensity.Bindings

open Set
open NavierStokes.ProblemStatement

section Correspondence

/-- The contract's `convectionDivergence` is the implementation's (unit E1,
`Section4/A01/ConvectionDivergence.lean`).  Drift-guards `projected`. -/
theorem regularityPartial_convectionDivergence_eq :
    Contracts.V1.RegularityPartial.convectionDivergence
      = NSFormalization.Section4.A01.convectionDivergence := rfl

/-- The contract's `HasSymmetricJacobian` is the implementation's restatement
(`Section4/A01/RadialPotential.lean`).  Referenced by no field of this version; the
contract reserves it for the excluded `pressure_recovery` (whose `IsLerayComplement`,
`Spec.lean:135`, uses this predicate). -/
theorem regularityPartial_hasSymmetricJacobian_eq :
    Contracts.V1.RegularityPartial.HasSymmetricJacobian
      = NSFormalization.Section4.A01.RadialPotential.HasSymmetricJacobian := rfl

/-- The contract's radial potential (reused from `Contracts/V1/Data.lean:596`, never
restated in `RegularityPartial`) is the implementation's `RadialPotential.pressurePotential`.
This is the load-bearing bridge `REVIEW_M4.md` finding 6 flagged: it is the only thing
tying `pressure_potential_of_classicalSolution` (which produces the `RadialPotential`
spelling) to the contract field (which uses the `Data` spelling). -/
theorem regularityPartial_pressurePotential_eq :
    Contracts.V1.Data.pressurePotential
      = NSFormalization.Section4.A01.RadialPotential.pressurePotential := rfl

end Correspondence

/-- Bind the two proved fields of the whole-space local-regularity interface to the
stable version-one contract.  `projected` and `pressure_potential` apply the
corresponding A01 theorem to the solution transported by `uniqueness_toA02`; the
conclusion is definitionally the contract's, since `(uniqueness_toA02 u).{velocity,
pressure}` reduce to `u.{velocity,pressure}` and the §0 bridges above (plus
`uniqueness_pressureGaugeEquivOn_eq`) identify the vocabulary.

`ManuscriptLocalRegularityPartialAPI` has only propositional fields, so it lives in
`Prop`; the binding is therefore a `theorem` rather than a `def`. -/
theorem regularityPartial :
    Contracts.V1.RegularityPartial.ManuscriptLocalRegularityPartialAPI where
  projected := fun ν a f T u =>
    NSFormalization.Section4.A01.projected_of_classicalSolution ν a f T (uniqueness_toA02 u)
  pressure_potential := fun _ν _a _f _T u =>
    NSFormalization.Section4.A01.PressureGauge.pressure_potential_of_classicalSolution
      (uniqueness_toA02 u)

end BlowupDensity.Bindings
