import NSFormalization.Section3.T23.Boundary

/-! T23 U8: interior packet witnesses and local essential-supremum blow-up. -/

noncomputable section
namespace NSFormalization.Section3.T23
open Set MeasureTheory Filter
open NavierStokes.ProblemStatement
open NSFormalization.Source.PacketScaling
open NSFormalization.Section3.T15 (scaledVelocity scaledVelocity_eq_parabolicVelocity)
open scoped Topology

/-- The I03 rescaling argument, before spatial periodization. -/
theorem scaledPacket_speedUnbounded {U : VelocityField} (hspeed : SpeedUnboundedAtOne U)
    {T ε : ℝ} (hε : 0 < ε) (htime : ε ^ 2 ≤ T) (x₀ : Space) :
    SpeedUnboundedAt T (scaledVelocity U x₀ T ε) := by
  have hinv : (((ε⁻¹ : ℝ) ^ 2)⁻¹) = ε ^ 2 := by rw [inv_pow, inv_inv]
  rw [scaledVelocity_eq_parabolicVelocity, ← hinv]
  exact speed_unbounded_at_target (inv_pos.mpr hε) (by simpa [hinv] using htime)
    x₀ (zeroPastField_speed hspeed)

end NSFormalization.Section3.T23
