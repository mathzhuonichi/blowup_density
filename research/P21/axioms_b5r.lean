import NSFormalization.Section4.A04.H1RestartBeyond
import Tests.ContinuationV3

#print axioms NSFormalization.Section4.A04.restartFixedForceH1
run_cmd BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section4.A04.restartFixedForceH1
#print axioms NSFormalization.Section4.A04.restartBeyondH1_le
run_cmd BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section4.A04.restartBeyondH1_le
#print axioms NSFormalization.Section4.A04.restartBeyondH1
run_cmd BlowupDensity.TestSupport.checkAxioms ``NSFormalization.Section4.A04.restartBeyondH1
#print axioms BlowupDensity.Bindings.continuationV3_holds
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Bindings.continuationV3_holds
#print axioms BlowupDensity.Tests.checkedContinuationV3
run_cmd BlowupDensity.TestSupport.checkAxioms ``BlowupDensity.Tests.checkedContinuationV3
