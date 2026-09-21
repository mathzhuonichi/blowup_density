import NSFormalization.Section4.A01.ForcingFamilyBound
noncomputable section
namespace NSFormalization.Section4.A01
open EulerCylinderSobolevSpace EulerLiftedGradientSpace
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
theorem rev200_sign_mutation {q : ℕ} (s p f b : SobolevSpace 1 (q+1))
    (t : SobolevWord (q+1) → LiftL2 1) (h : s+p = f-b) :
    (fun w => s.val w + t w + p.val w) = f.val + (t+b.val) := by
  funext w
  have hw : s.val w + p.val w = f.val w - b.val w := congrArg (fun z => z.val w) h
  change _ = f.val w + (t w - b.val w)
  rw [add_right_comm, hw]
  abel


end NSFormalization.Section4.A01
