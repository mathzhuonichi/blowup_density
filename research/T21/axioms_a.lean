import Tests.TorusNonDensity
import Tests.TorusMain

/-! Transitive axiom audit for T21 unit A.  Every declaration below must print
exactly `[propext, Classical.choice, Quot.sound]`. -/

-- Canonical final assembly.
#print axioms NSFormalization.Section3.T21.mainStatement
#print axioms NSFormalization.Section3.T21.mainOfDensityAndNonDensity
#print axioms NSFormalization.Section3.T21.mainOfInputs
#print axioms NSFormalization.Section3.T21.nonDensityOfCritical_holds
#print axioms NSFormalization.Section3.T21.mainOfDensityAndNonDensity_arrow_holds
#print axioms NSFormalization.Section3.T21.mainOfInputs_holds
#print axioms NSFormalization.Section3.T21.closedNonDensityAPI
#print axioms NSFormalization.Section3.T21.closedMainTheoremAPI
#print axioms NSFormalization.Section3.T21.nonemptyNonDensityAPI
#print axioms NSFormalization.Section3.T21.nonemptyMainTheoremAPI
#print axioms NSFormalization.Section3.T21.exists_nonemptyNonDensityAPI
#print axioms NSFormalization.Section3.T21.nonDensityStatement_unconditional
#print axioms NSFormalization.Section3.T21.mainStatement_holds

-- Contract declarations.
#print axioms BlowupDensity.Contracts.V1.TorusNonDensity.breakdownSetTZero
#print axioms BlowupDensity.Contracts.V1.TorusNonDensity.criticalBallT
#print axioms BlowupDensity.Contracts.V1.TorusNonDensity.NonDensityAPI
#print axioms BlowupDensity.Contracts.V1.TorusNonDensity.nonDensityStatement
#print axioms BlowupDensity.Contracts.V1.TorusNonDensity.nonDensityOfCritical
#print axioms BlowupDensity.Contracts.V1.TorusMain.MainTheoremAPI
#print axioms BlowupDensity.Contracts.V1.TorusMain.mainStatement
#print axioms BlowupDensity.Contracts.V1.TorusMain.mainOfDensityAndNonDensity
#print axioms BlowupDensity.Contracts.V1.TorusMain.mainOfInputs

-- Non-density binding and closure.
#print axioms BlowupDensity.Bindings.TorusNonDensity.criticalBallT_eq
#print axioms BlowupDensity.Bindings.TorusNonDensity.breakdownSetTZero_eq
#print axioms BlowupDensity.Bindings.TorusNonDensity.criticalBallDisjoint
#print axioms BlowupDensity.Bindings.TorusNonDensity.ballDisjoint
#print axioms BlowupDensity.Bindings.TorusNonDensity.nonDensity
#print axioms BlowupDensity.Bindings.TorusNonDensity.nonDensityAPI
#print axioms BlowupDensity.Bindings.TorusNonDensity.nonDensityOfCritical_holds
#print axioms BlowupDensity.Bindings.TorusNonDensity.closedNonDensityAPI
#print axioms BlowupDensity.Bindings.TorusNonDensity.nonemptyNonDensityAPI
#print axioms BlowupDensity.Bindings.TorusNonDensity.exists_nonemptyNonDensityAPI
#print axioms BlowupDensity.Bindings.TorusNonDensity.nonDensityStatement_holds

-- Main binding and public checks.
#print axioms BlowupDensity.Bindings.TorusMain.mainTheoremAPI
#print axioms BlowupDensity.Bindings.TorusMain.mainOfDensityAndNonDensity_holds
#print axioms BlowupDensity.Bindings.TorusMain.mainOfInputs_holds
#print axioms BlowupDensity.Bindings.TorusMain.closedMainTheoremAPI
#print axioms BlowupDensity.Bindings.TorusMain.nonemptyMainTheoremAPI
#print axioms BlowupDensity.Bindings.TorusMain.mainStatement_holds
#print axioms BlowupDensity.Tests.checkedTorusNonDensity
#print axioms BlowupDensity.Tests.checkedTorusMain
