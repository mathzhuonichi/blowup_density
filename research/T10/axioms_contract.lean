import Tests.TorusData

/-!
# T01.torus_data conformance and transitive axiom audit

Run from `verification/` with
`lake env lean ../research/T10/axioms_contract.lean`.
-/

open MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Bindings
open scoped ENNReal

#print axioms periodicTorus_eq
#print axioms periodicTorusMeasure_eq
#print axioms torusLift_eq
#print axioms periodicFourierCoeff_eq
#print axioms realPeriodicSubmodule_eq
#print axioms periodicSobolev_eq
#print axioms isPeriodicDatum_eq
#print axioms isPeriodicHomogeneousDatum_eq
#print axioms isPeriodicReweight_eq
#print axioms torusData
#print axioms BlowupDensity.Tests.checkedTorusData

/-- Literal conformance with the amended `Spec.lean` forward Parseval field. -/
example :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure :=
  torusData.parseval_forward

/-- Literal conformance with the `Spec.lean` Leray contraction field. -/
example :
    ∀ (s : ℝ) (A : PeriodicSobolev s),
      ∃ B : PeriodicSobolev s,
        IsPeriodicLerayDatum A B ∧ ‖B‖ ≤ ‖A‖ ∧ IsSolenoidalPeriodicDatum B :=
  torusData.leray_exists_contraction
