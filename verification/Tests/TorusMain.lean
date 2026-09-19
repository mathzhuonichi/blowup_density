import Contracts.V1.TorusMain
import Bindings.TorusMain
import TestSupport.Axioms

/-! Public statement, field-shape, arrow, and axiom checks for `T03.main` V1. -/

noncomputable section

namespace BlowupDensity.Tests

open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusNonDensity
open BlowupDensity.Contracts.V1.TorusMain

/-- Checked `thm:main` (`03-torus.tex:6-16`). -/
theorem checkedTorusMain : mainStatement :=
  Bindings.TorusMain.mainStatement_holds

run_cmd TestSupport.checkAxioms ``checkedTorusMain

/-- The complete five-field record is closed. -/
example : Nonempty MainTheoremAPI :=
  Bindings.TorusMain.nonemptyMainTheoremAPI

/-- Conformance with the density/non-density assembly arrow. -/
example : mainOfDensityAndNonDensity :=
  Bindings.TorusMain.mainOfDensityAndNonDensity_holds

/-- Conformance with the registered T19/T20 two-input arrow. -/
example : mainOfInputs :=
  Bindings.TorusMain.mainOfInputs_holds

/-- Clause (ii) retains every real order, including negative orders. -/
example : ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T → ∀ s : ℝ,
    RelativelyDenseT 1 s forceClassT (breakdownSetTZero ν T) ↔ s < 1 / 2 :=
  Bindings.TorusMain.closedMainTheoremAPI.zeroInitialDensityIff

end BlowupDensity.Tests
