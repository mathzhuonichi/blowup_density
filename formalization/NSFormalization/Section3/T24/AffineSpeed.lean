import NSFormalization.Section3.T24.AffineBasics

/-!
# T24a Ua5: unbounded speed of affine variations

An admissible affine variation vanishes after `τ₁`.  Since `τ₁ < 1`, every
left neighborhood of the singular time contains a smaller neighborhood on
which the affine velocity agrees with the original packet velocity.
-/

noncomputable section

namespace NSFormalization.Section3.T24

open Set
open NavierStokes.ProblemStatement

/-- `AffineVariationAPI.speed_unbounded` (`research/T24/Spec.lean:1069`),
stated over the raw packet velocity and its raw `SpeedUnboundedAtOne` clause.

The separate hypothesis `τ₁ < 1` is necessary because `AffineAdmissible`
constrains the variation relative to the supplied cylinder but does not assert
that the cylinder's time window lies below the singular time. -/
theorem speed_unbounded {U : VelocityField} (c : Space) (r τ₀ τ₁ : ℝ)
    (hτ₁ : τ₁ < 1) (hspeed : SpeedUnboundedAtOne U) :
    ∀ b : VelocityField, AffineAdmissible c r τ₀ τ₁ b →
      SpeedUnboundedAtOne (affineVelocity U b) := by
  intro b hb M hM δ hδ
  have hwidth : 0 < min δ (1 - τ₁) :=
    lt_min hδ (sub_pos.mpr hτ₁)
  obtain ⟨t, x, ht, ht_near, ht_large⟩ :=
    hspeed M hM (min δ (1 - τ₁)) hwidth
  have hτ₁t : τ₁ ≤ t := by
    have hmin : min δ (1 - τ₁) ≤ 1 - τ₁ := min_le_right _ _
    linarith
  refine ⟨t, x, ht, ?_, ?_⟩
  · have hmin : min δ (1 - τ₁) ≤ δ := min_le_left _ _
    linarith
  · rw [late_agreement b hb t hτ₁t x]
    exact ht_large

end NSFormalization.Section3.T24
