import Contracts.V1.TorusMain
import Bindings.TorusNonDensity
import Bindings.Density
import NSFormalization.Section3.T21.MainAssembly

/-!
# Binding for the main torus density threshold
-/

noncomputable section

namespace BlowupDensity.Bindings.TorusMain

open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1.TorusNonDensity
open BlowupDensity.Contracts.V1.TorusMain

/-- Assemble the five registered fields from the two inputs named at
`03-torus.tex:523`. -/
theorem mainTheoremAPI
    (D : BlowupDensity.Contracts.V1.Density.PeriodicDensityAPI)
    (N : NonDensityAPI c) : MainTheoremAPI where
  thresholdValue := D.thresholdValue
  zeroInitialClass := NSFormalization.Section3.T21.zeroInitialClass
  fixedInitialDensity := D.fixedInitialDensity
  zeroInitialDensityIff := by
    intro ν hν T hT s
    constructor
    · intro hdense
      by_contra hs
      exact N.nonDensity ν hν s (le_of_not_gt hs) T hT hdense
    · intro hs
      exact D.fixedInitialDensity (fun _ : Space ↦ 0)
        NSFormalization.Section3.T21.zeroInitialClass ν hν T hT s hs
  zeroInitialNonDensity := by
    intro ν hν T hT s hs
    exact N.nonDensity ν hν s hs T hT

/-- The registered density/non-density arrow is inhabited. -/
theorem mainOfDensityAndNonDensity_holds : mainOfDensityAndNonDensity :=
  fun _c D N ↦ mainTheoremAPI D N

/-- The registered T19/T20 two-input arrow is inhabited. -/
theorem mainOfInputs_holds : mainOfInputs :=
  fun D K ↦ mainTheoremAPI D (TorusNonDensity.nonDensityAPI K)

/-- The closed registered five-field package. -/
theorem closedMainTheoremAPI : MainTheoremAPI :=
  mainTheoremAPI Density.periodicDensityAPI
    TorusNonDensity.closedNonDensityAPI

/-- Closed registered record non-vacuity. -/
theorem nonemptyMainTheoremAPI : Nonempty MainTheoremAPI :=
  ⟨closedMainTheoremAPI⟩

/-- The registered paper statement is closed unconditionally. -/
theorem mainStatement_holds : mainStatement :=
  ⟨closedMainTheoremAPI.fixedInitialDensity,
    closedMainTheoremAPI.zeroInitialDensityIff⟩

end BlowupDensity.Bindings.TorusMain
