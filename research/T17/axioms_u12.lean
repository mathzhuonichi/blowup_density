import Tests.Correction3

-- Canonical assembly, all 45 fields and the completed G4 closure.
#print axioms NSFormalization.Section3.T17.correctionAPI_of_smooth
#print axioms NSFormalization.Section3.T17.correctionStatementAmended_holds
#print axioms NSFormalization.Section3.T17.Nonvacuity.chart_in_cube
#print axioms NSFormalization.Section3.T17.Nonvacuity.place
#print axioms NSFormalization.Section3.T17.Nonvacuity.reference_nonzero
#print axioms NSFormalization.Section3.T17.Nonvacuity.nonvacuous_correction

-- Complete record conversions and the registered theorem/non-vacuity.
#print axioms BlowupDensity.Bindings.Correction3.ofContract
#print axioms BlowupDensity.Bindings.Correction3.toContract
#print axioms BlowupDensity.Bindings.Correction3.ofPacket
#print axioms BlowupDensity.Bindings.Correction3.toPacket
#print axioms BlowupDensity.Bindings.Correction3.correctionStatement_iff
#print axioms BlowupDensity.Bindings.Correction3.correctionStatementAmended_iff
#print axioms BlowupDensity.Bindings.Correction3.Packet.correctionStatement_iff
#print axioms BlowupDensity.Bindings.Correction3.correctionStatementAmended_holds
#print axioms BlowupDensity.Bindings.Correction3.nonvacuous_correction
#print axioms BlowupDensity.Tests.checkedCorrection3
#print axioms BlowupDensity.Tests.checkedCorrection3_nonvacuous

-- Definitional bridges and round trips may need fewer than the three permitted
-- logical axioms; audit their actual transitive dependencies as well.
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.Correction3.to_of
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.Correction3.of_to
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.Correction3.toPacket_ofPacket
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.Correction3.ofPacket_toPacket
