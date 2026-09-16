import NSFormalization.Section4.A01.LerayBridge

noncomputable section
namespace NSFormalization.Section4.A01

open NSFormalization.Paper3
open NSFormalization.Section4.D01

-- Reject the wrong-sign mutation, then check the correct sign, within the hard cap.
set_option maxHeartbeats 400000 in
theorem projected_datum_of_decomposition_sign_check
    (A P G : RealVectorSobolev 0)
    (hdecomp : A = P + G)
    (hsol : Leray.lerayComplement 0 P = 0)
    (hgrad : Leray.lerayComplement 0 G = G) :
    P = A - Leray.lerayComplement 0 A := by
  fail_if_success
    have hwrong : P = A + Leray.lerayComplement 0 A := by
      rw [hdecomp, map_add, hsol, hgrad, zero_add, add_sub_cancel_right]
  exact projected_datum_of_decomposition A P G hdecomp hsol hgrad

end NSFormalization.Section4.A01
