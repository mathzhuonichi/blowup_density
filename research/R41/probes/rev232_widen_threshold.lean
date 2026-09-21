import NSFormalization.Section4.R41.NonDensity

open scoped ENNReal

namespace NSFormalization.Section4.R41
open A02 (SpaceTimeField)
open D01

/-! Reviewer mutation: widen the claimed non-density range by one Sobolev order.
The production proof is copied unchanged; it must fail when recovering the true
endpoint hypotheses in both exponent cases. -/
theorem rev232_widened_nonDensityZero_of_q (thresholds : RMainThresholds) :
    ∀ q : ℝ, (q = 1 ∨ q = 2) →
      ∀ ν T : ℝ, 0 < ν → 0 < T →
        ∀ s : ℝ, thresholds.exponent q 0 - 1 ≤ s →
          ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ breakdownSetRZero ν T,
            ENNReal.ofReal ρ ≤ forceSobolevENorm (ENNReal.ofReal q) s f := by
  rintro q (rfl | rfl) ν T hν hT s hs
  · have hs' : 1 / 2 ≤ s := by
      rw [thresholds.l1] at hs
      norm_num at hs ⊢
      exact hs
    refine ⟨R43.criticalConst * ν, mul_pos R43.criticalConst_pos hν, ?_⟩
    intro f hf
    simpa using criticalRadius_le_forceSobolevENorm hν hs' hf
  · have hs' : -1 / 2 ≤ s := by
      rw [thresholds.l2] at hs
      norm_num at hs ⊢
      exact hs
    refine ⟨R44.radius ν T, R44.radius_pos hν, ?_⟩
    intro f hf
    simpa using radius_le_forceSobolevENorm_L2 hν hT hs' hf

end NSFormalization.Section4.R41
