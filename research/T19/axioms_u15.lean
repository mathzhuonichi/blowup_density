import Tests.Density

/-! Transitive axiom audit for the T19 U15 assembly and registration. -/

-- Canonical assembly.
#print axioms NSFormalization.Section3.T19.periodicDensityAPI
#print axioms NSFormalization.Section3.T19.mixedRegionAPI
#print axioms NSFormalization.Section3.T19.strongClosureAPI
#print axioms NSFormalization.Section3.T19.projectionAPI
#print axioms NSFormalization.Section3.T19.periodicDensityStatement_holds
#print axioms NSFormalization.Section3.T19.mixedRegionStatement_holds
#print axioms NSFormalization.Section3.T19.strongClosureStatement_holds
#print axioms NSFormalization.Section3.T19.projectionStatement_holds

-- Contract vocabulary, records, and headline statements.
#print axioms BlowupDensity.Contracts.V1.Density.RegularTrajectoryT
#print axioms BlowupDensity.Contracts.V1.Density.SingularTrajectoryT
#print axioms BlowupDensity.Contracts.V1.Density.extendedBreakdownSetT
#print axioms BlowupDensity.Contracts.V1.Density.spaceTimeL2L2ENormT
#print axioms BlowupDensity.Contracts.V1.Density.RelativelyDenseMixedT
#print axioms BlowupDensity.Contracts.V1.Density.PeriodicDensityAPI
#print axioms BlowupDensity.Contracts.V1.Density.MixedRegionAPI
#print axioms BlowupDensity.Contracts.V1.Density.StrongClosureAPI
#print axioms BlowupDensity.Contracts.V1.Density.ProjectionAPI
#print axioms BlowupDensity.Contracts.V1.Density.periodicDensityStatement
#print axioms BlowupDensity.Contracts.V1.Density.mixedRegionStatement
#print axioms BlowupDensity.Contracts.V1.Density.strongClosureStatement
#print axioms BlowupDensity.Contracts.V1.Density.projectionStatement

-- Definitional and structure-exception binding declarations.
#print axioms BlowupDensity.Bindings.Density.criticalOrder_eq
#print axioms BlowupDensity.Bindings.Density.mixedLebesgueENormT_eq
#print axioms BlowupDensity.Bindings.Density.spaceTimeL2L2ENormT_eq
#print axioms BlowupDensity.Bindings.Density.relativelyDenseMixedT_eq
#print axioms BlowupDensity.Bindings.Density.regularTrajectory_toCanonical
#print axioms BlowupDensity.Bindings.Density.regularTrajectory_toContract
#print axioms BlowupDensity.Bindings.Density.singularTrajectory_toCanonical
#print axioms BlowupDensity.Bindings.Density.singularTrajectory_toContract
#print axioms BlowupDensity.Bindings.Density.extendedBreakdownSetT_eq
#print axioms BlowupDensity.Bindings.Density.periodicDensityAPI
#print axioms BlowupDensity.Bindings.Density.mixedRegionAPI
#print axioms BlowupDensity.Bindings.Density.strongClosureAPI
#print axioms BlowupDensity.Bindings.Density.projectionAPI
#print axioms BlowupDensity.Bindings.Density.periodicDensityStatement_holds
#print axioms BlowupDensity.Bindings.Density.mixedRegionStatement_holds
#print axioms BlowupDensity.Bindings.Density.strongClosureStatement_holds
#print axioms BlowupDensity.Bindings.Density.projectionStatement_holds

-- Public checks.
#print axioms BlowupDensity.Tests.checkedPeriodicDensity
#print axioms BlowupDensity.Tests.checkedMixedRegion
#print axioms BlowupDensity.Tests.checkedStrongClosure
#print axioms BlowupDensity.Tests.checkedProjection
#print axioms BlowupDensity.Tests.checkedDensity
