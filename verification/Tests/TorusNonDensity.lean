import Contracts.V1.TorusNonDensity
import Bindings.TorusNonDensity
import TestSupport.Axioms

/-! Public statement, field-shape, arrow, and axiom checks for
`T03.non_density` V1. -/

noncomputable section

namespace BlowupDensity.Tests

open Set
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusNonDensity
open scoped ENNReal

/-- Checked `cor:nondensity` (`03-torus.tex:506-520`). -/
theorem checkedTorusNonDensity : nonDensityStatement :=
  Bindings.TorusNonDensity.nonDensityStatement_holds

run_cmd TestSupport.checkAxioms ``checkedTorusNonDensity

/-- The complete registered record is nonempty at the explicit canonical T20
constant, rather than at an unconstrained witness. -/
example : Nonempty
    (NonDensityAPI NSFormalization.Section3.T20.criticalSmallnessH1) :=
  Bindings.TorusNonDensity.nonemptyNonDensityAPI

/-- The witness-independent existential is also available. -/
example : ∃ c : ℝ, Nonempty (NonDensityAPI c) :=
  Bindings.TorusNonDensity.exists_nonemptyNonDensityAPI

/-- Conformance with the critical-order zero-force specialization. -/
example : (0 : SpaceTimeField) ∈
    criticalBallT NSFormalization.Section3.T20.criticalSmallnessH1 1 (1 / 2) :=
  Bindings.TorusNonDensity.closedNonDensityAPI.zeroMemBall 1 zero_lt_one (1 / 2)

/-- Conformance with the registered critical-to-non-density arrow. -/
example : nonDensityOfCritical :=
  Bindings.TorusNonDensity.nonDensityOfCritical_holds

end BlowupDensity.Tests
