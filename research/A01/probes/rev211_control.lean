import NSFormalization.Section4.A01.LocalTheoryBundle
noncomputable section
namespace NSFormalization.Section4.A01
open Set MeasureTheory EulerSmoothLimit EulerLpTranslation EulerMeanOrdinaryLift
  EulerMeanSmoothRepresentative EulerCylinderSobolevSpace EulerLiftedGradientSpace
  EulerSmoothFieldSobolevTime EulerQuadraticSource EulerVolterraConvolution
open D01 (IsSobolevDatum)
open scoped ENNReal
theorem control_positive_horizon :
    ∀ ν, 0 < ν → ∀ f, D01.MemForceR f → ∀ K : ℝ≥0∞, K ≠ ⊤ →
      ∃ δ > 0, ∀ a, a ∈ A02.initialClassR → D01.sobolevENorm 7 a ≤ K →
        δ ≤ localHorizon' ν a f := by
  intro ν hν f hf K hK
  refine ⟨uniformHorizon ν (datumRadiusConstant * K.toReal) ‖referenceForce f hf‖,
    uniformHorizon_pos _ _ _, ?_⟩
  intro a ha hbound
  rw [localHorizon'_eq hν ha hf]
  apply uniformHorizon_antitone ν _ le_rfl
  obtain ⟨D, hD⟩ := ha.1.2 7
  have hD' : IsSobolevDatum 7 (selectedDatum a ha).field D := by
    rw [(selectedDatum_spec a ha).1]
    exact hD
  have hn : ‖D‖ ≤ K.toReal := by
    have h := ENNReal.toReal_mono hK hbound
    have heq : D01.sobolevENorm 7 a = ‖D‖ₑ := A04.sobolevENorm_eq hD
    rw [heq] at h
    simpa only [toReal_enorm] using h
  exact (cylinderDatum_norm_le (selectedDatum a ha) D hD').trans
    (mul_le_mul_of_nonneg_left hn datumRadiusConstant_nonneg)

end NSFormalization.Section4.A01
