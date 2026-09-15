-- Reviewer probe (lane 140 review, REVIEW_EULER_PAIRING.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.A01.EulerPairing
open EulerCylinderSobolevSpace EulerMeanOrdinaryLift
open NavierStokes.ProblemStatement
set_option pp.fullNames true in
#check fun {q : ℕ} (u : SobolevSpace 1 q) => u.val
