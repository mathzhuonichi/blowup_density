import Euler.PacketCylinderJetParity
import Euler.PacketCylinderAngularRegularity

/-! Literal angular averaging preserves the joint odd parity of a genuine periodic field. -/

noncomputable section

namespace EulerPacketCylinderField.Field

open Set EulerSmoothLimit EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)

include G in
theorem angleMean_odd (hodd : JointOdd T raw) :
    JointOdd T (EulerPacketProfileRecursion.angleMean P raw) := by
  intro t x θ
  have he : (fun s : ℝ => raw (t,(-x,s))) = fun s : ℝ => -raw (t,(x,-s)) := by
    funext s
    simpa only [neg_neg] using hodd t x (-s)
  have hs := (G.raw_periodic t x).intervalIntegral_add_eq (-P) 0
  simp only [neg_add_cancel,zero_add] at hs
  change P⁻¹ • (∫ s in (0 : ℝ)..P,raw (t,(-x,s))) =
    -(P⁻¹ • (∫ s in (0 : ℝ)..P,raw (t,(x,s))))
  rw [he,intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg (f := fun s : ℝ => raw (t,(x,s))),neg_zero,hs,smul_neg]

end EulerPacketCylinderField.Field
