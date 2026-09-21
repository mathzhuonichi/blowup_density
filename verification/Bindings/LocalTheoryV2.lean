import Contracts.V2.LocalTheory
import Bindings.MaximalPartial
import NSFormalization.Section4.A01.LocalTheoryBundle

/-!
# Binding the A01 version-two local-theory contract

The implementation chooses `localHorizon'` and the carrier-bundled solution
`localCarrier`; lane 211 proves full manuscript regularity for that exact
solution and the fixed-force H⁷ horizon bound.

The contract and `Section4/A02` solution classes are distinct structures.
This file therefore reuses the field-wise conversions
`uniqueness_toA02` / `maximalPartial_ofA02`, records their full round trips,
and transports `ManuscriptLocalRegularity` field by field.  All ordinary
definitions copied into the contract have explicit `rfl` bridges below.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V2
open NSFormalization.Section4
open scoped ENNReal

/-! ## Definition correspondence -/

/-- The contract's tensor-divergence definition is the implementation's. -/
theorem localTheoryV2_convectionDivergence_eq :
    LocalTheory.convectionDivergence = A01.convectionDivergence := rfl

/-- The contract's symmetric-Jacobian predicate is the implementation's. -/
theorem localTheoryV2_hasSymmetricJacobian_eq :
    LocalTheory.HasSymmetricJacobian = A01.RadialPotential.HasSymmetricJacobian := rfl

/-- The contract's Helmholtz-complement characterization is the implementation's. -/
theorem localTheoryV2_isLerayComplement_eq :
    LocalTheory.IsLerayComplement = A01.IsLerayComplement := rfl

/-- The radial pressure potential reused from V1 data is the implementation's
restatement. -/
theorem localTheoryV2_pressurePotential_eq :
    Contracts.V1.Data.pressurePotential = A01.RadialPotential.pressurePotential := rfl

/-- The physical H⁷ norm used by the contract is the D01 implementation norm. -/
theorem localTheoryV2_sobolevENorm_eq :
    Contracts.V1.Data.sobolevENorm = NSFormalization.Section4.D01.sobolevENorm := rfl

/-! ## Structure conversion and regularity transport -/

/-- The A02-to-contract and contract-to-A02 solution conversions are inverse
on the full structure, not only on the velocity and pressure projections. -/
theorem localTheoryV2_toA02_ofA02 {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : A02.ClassicalSolutionR ν a f T) :
    uniqueness_toA02 (maximalPartial_ofA02 w) = w := by
  cases w
  rfl

/-- The opposite full round trip for the canonical contract solution class. -/
theorem localTheoryV2_ofA02_toA02 {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} (w : ClassicalSolutionR ν a f T) :
    maximalPartial_ofA02 (uniqueness_toA02 w) = w := by
  cases w
  rfl

/-- Move the implementation's full regularity record across the two solution
classes and the three definition bridges, field by field. -/
theorem localTheoryV2_regularity_ofA02 {ν : ℝ} {a : SpatialField} {f : SpaceTimeField}
    {T : ℝ} {w : A02.ClassicalSolutionR ν a f T}
    (h : A01.ManuscriptLocalRegularity ν a f T w) :
    LocalTheory.ManuscriptLocalRegularity ν a f T (maximalPartial_ofA02 w) where
  sobolev_smooth := h.sobolev_smooth
  pressure_recovery := h.pressure_recovery
  projected := h.projected
  pressure_potential := h.pressure_potential

/-! ## Registered witness -/

/-- The owner-approved version-two A01 witness: the inherited V1 facts,
lane 211's named local solution and full regularity, and its fixed-force H⁷
uniform lower bound.

The two inherited fields are filled from the same implementation theorems as
V1.  We cannot import `Bindings.RegularityPartial` in this module because its
older proof path imports `ProjectedEquation.lean`, whose theorem name is also
exported by the later all-four-fields assembly `ManuscriptRegularity.lean`.
The frozen V1 test still checks its original binding independently; the
projection below is the structural compatibility link. -/
def localTheoryV2 : LocalTheory.LocalTheoryAPI :=
  { projected := fun _ν _a _f _T u =>
      A01.projected_of_classicalSolution (uniqueness_toA02 u)
    pressure_potential := fun _ν _a _f _T u =>
      A01.PressureGauge.pressure_potential_of_classicalSolution (uniqueness_toA02 u)
    horizon := A01.localHorizon'
    solution := fun ν a f hν ha hf =>
      maximalPartial_ofA02 (A01.localCarrier ν a f hν ha hf).w
    regularity := fun ν a f hν ha hf =>
      localTheoryV2_regularity_ofA02
        (A01.manuscriptLocalRegularity_localCarrier ν a f hν ha hf)
    horizon_lower_bound := A01.horizon_lower_bound_H7_fixedForce }

end BlowupDensity.Bindings
