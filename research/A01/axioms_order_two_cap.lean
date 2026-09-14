-- Conformance: every declaration of `Section4/A01/OrderTwoCap.lean` depends only on the
-- three standard logical axioms `[propext, Classical.choice, Quot.sound]`.
-- Plus a cheap non-vacuity witness: the zero cylinder field satisfies every hypothesis of
-- deliverable 1, so the constructor delivers a genuine `HasWeakDerivsL2Bound` conclusion.
-- Run: cd verification && lake env lean ../research/A01/axioms_order_two_cap.lean
import NSFormalization.Section4.A01.OrderTwoCap

noncomputable section
namespace NSFormalization.Section4.A01
open NSFormalization.Section4.D01
open EulerMeanOrdinaryLift EulerCylinderSobolevSpace

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Non-vacuity (concrete, cheap): the zero cylinder value `0 : SobolevSpace 1 (q+1)` is
angle-invariant and its ordinary lift is `value 1 0`, so deliverable 1 fires and produces
`HasWeakDerivsL2Bound 0 0 2` (here `‖(0)‖² = 0`). -/
example (q : ℕ) (hm : (2 : ℕ) + 3 ≤ q + 1) :
    HasWeakDerivsL2Bound (⇑(0 : EulerMeanSolenoidal.L2)) (‖(0 : SobolevSpace 1 (q + 1))‖ ^ 2) 2 :=
  hasWeakDerivsL2Bound_of_cylinder (0 : SobolevSpace 1 (q + 1))
    (fun θ => by simp) (0 : EulerMeanSolenoidal.L2) (by simp [value]) 2 hm

end NSFormalization.Section4.A01

open NSFormalization.Section4.A01

#print axioms norm_word_le
#print axioms eLpNorm_descend_le
#print axioms hasWeakDerivsL2Bound_of_word
#print axioms hasWeakDerivsL2Bound_of_cylinder
#print axioms sobolevENorm_two_toReal_le
#print axioms sobolevENorm_two_ne_top
#print axioms sobolevNormAt_two_le_of_cylinder
#print axioms sobolevNormAt_two_sq_le_of_sup
#print axioms kbnd_of_sup_bound
