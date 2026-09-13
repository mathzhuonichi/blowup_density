import NSFormalization.Source.RieszPotentialTail
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A bounded near-field Riesz estimate

This module records the elementary conditional interface for the near field.
The hypothesis is an explicit essential pointwise bound on the weighted
integrand.  It is deliberately weaker than, and independent of, any maximal
operator theorem: no Hardy--Littlewood estimate is asserted here.
-/

open MeasureTheory Set Real
open scoped ENNReal

namespace NSFormalization.RieszPotentialNearField

abbrev Space := NSFormalization.RieszPotentialTail.Space

theorem nearField_lintegral_bound_bounded
    {a R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B)
    {g : Space → ℂ} (x : Space)
    (hbound : ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Space) R),
      ‖y‖ ^ (a - 3) * ‖g (x - y)‖ ≤ B) :
    ∫⁻ y in Metric.ball (0 : Space) R,
      ENNReal.ofReal (‖y‖ ^ (a - 3) * ‖g (x - y)‖) ∂volume
      ≤ ENNReal.ofReal B * volume (Metric.ball (0 : Space) R) := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : Space) R)]
      (fun y : Space => ‖y‖ ^ (a - 3) * ‖g (x - y)‖) :=
    Filter.Eventually.of_forall (fun y => mul_nonneg
      (Real.rpow_nonneg (norm_nonneg y) _) (norm_nonneg _))
  have hof : ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Space) R),
      ENNReal.ofReal (‖y‖ ^ (a - 3) * ‖g (x - y)‖) ≤ ENNReal.ofReal B := by
    filter_upwards [hbound] with y hy
    exact ENNReal.ofReal_le_ofReal hy
  calc
    ∫⁻ y in Metric.ball (0 : Space) R,
        ENNReal.ofReal (‖y‖ ^ (a - 3) * ‖g (x - y)‖) ∂volume
        ≤ ∫⁻ _y in Metric.ball (0 : Space) R, ENNReal.ofReal B ∂volume :=
          lintegral_mono_ae hof
    _ = ENNReal.ofReal B * volume (Metric.ball (0 : Space) R) := by
      rw [lintegral_const]
      simp

theorem ball_volume_fin_three_pos {R : ℝ} (hR : 0 < R) :
    volume (Metric.ball (0 : Space) R) = ENNReal.ofReal R ^ 3 * ENNReal.ofReal (4 * Real.pi / 3) ∧
      0 < volume (Metric.ball (0 : Space) R) := by
  constructor
  · simpa [mul_comm] using (EuclideanSpace.volume_ball_fin_three (0 : Space) R)
  · rw [EuclideanSpace.volume_ball_fin_three]
    positivity

end NSFormalization.RieszPotentialNearField
