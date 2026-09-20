import Contracts.V1.TorusData
import Bindings.TorusData
import TestSupport.Axioms

/-! Public-type, Spec-field conformance, and transitive-axiom checks for T01 V1. -/

noncomputable section

namespace BlowupDensity.Tests

open MeasureTheory
open NavierStokes.ProblemStatement
open Contracts.V1.Data
open Contracts.V1.TorusData
open scoped ENNReal

/-- The implementation supplies all ten fields of the periodic data contract. -/
theorem checkedTorusData : Contracts.V1.TorusData.TorusDataAPI :=
  Bindings.torusData

run_cmd TestSupport.checkAxioms ``checkedTorusData

/-- Conformance with `research/T10/Spec.lean` field `parseval_forward`,
including the lead-amendment `MemLp` hypothesis in its exact position. -/
example :
    ∀ (z : SpatialField) (A : PeriodicSobolev 0), IsPeriodicDatum 0 z A →
      MemLp (torusLift z) 2 periodicTorusMeasure →
      ‖A‖ₑ = eLpNorm (torusLift z) 2 periodicTorusMeasure :=
  checkedTorusData.parseval_forward

end BlowupDensity.Tests
