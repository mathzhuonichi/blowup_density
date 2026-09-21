-- Reviewer probe (lane 140 review, REVIEW_EULER_PAIRING.md), preserved verbatim; compiles on this branch.
import NSFormalization.Section4.A01.EulerPairing
open EulerCylinderSobolevSpace EulerMeanOrdinaryLift
open NavierStokes.ProblemStatement

-- half of the A3-L1·k route: the array-coordinate bound
example {q n : ℕ} (u : SobolevSpace 1 q) (hn : n ≤ q) (w : Fin n → Fin 4) :
    ‖word 1 u hn w‖ ≤ ‖u‖ := norm_le_pi_norm u.val _

-- and ordinaryLift is an isometry
example (Zw : EulerMeanSolenoidal.L2) : ‖ordinaryLift Zw‖ = ‖Zw‖ := ordinaryLift.norm_map Zw
