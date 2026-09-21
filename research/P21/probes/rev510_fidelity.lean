import research.P21.Targets
import Tests.ContinuationV3

/-!
# Reviewer fidelity probe for lane 510

The two checked V3 fields inhabit the actual target propositions, rather than
copies of their displayed statements.
-/

namespace BlowupDensity.Research.P21.Rev510

theorem restart_target_exact : h1RestartR :=
  Tests.checkedContinuationV3.restartH1

theorem endpoint_target_exact : h1UniformEndpointR :=
  Tests.checkedContinuationV3.restartBeyondH1

end BlowupDensity.Research.P21.Rev510
