import NSFormalization.Section3.T19.Density

/-!
# T19 U-CAN transitive-axiom audit

Every declaration introduced by the canonical statement module must remain in
Lean's standard `[propext, Classical.choice, Quot.sound]` footprint.  This file
constructs no inhabitant of any of the four records.
-/

#print axioms NSFormalization.Section3.T19.RegularTrajectoryT
#print axioms NSFormalization.Section3.T19.SingularTrajectoryT
#print axioms NSFormalization.Section3.T19.extendedBreakdownSetT
#print axioms NSFormalization.Section3.T19.RelativelyDenseMixedT
#print axioms NSFormalization.Section3.T19.PeriodicDensityAPI
#print axioms NSFormalization.Section3.T19.periodicDensityStatement
#print axioms NSFormalization.Section3.T19.MixedRegionAPI
#print axioms NSFormalization.Section3.T19.mixedRegionStatement
#print axioms NSFormalization.Section3.T19.StrongClosureAPI
#print axioms NSFormalization.Section3.T19.strongClosureStatement
#print axioms NSFormalization.Section3.T19.ProjectionAPI
#print axioms NSFormalization.Section3.T19.projectionStatement
