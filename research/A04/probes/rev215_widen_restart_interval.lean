import NSFormalization.Section4.A04.RestartFixedForce

noncomputable section
namespace NSFormalization.Section4.A04

open Set
open NSFormalization.Section4.A02
open NSFormalization.Section4.D01 (sobolevENorm)
open EulerSmoothFieldSobolevTime EulerCylinderSobolevSpace
open scoped ENNReal

/- Reviewer mutation: widen the main restart-time interval from `[0,S]` to
`[0,S+1]`, while deliberately retaining the original proof and force window. -/
def RestartFixedForceWide (ν : ℝ) (f : SpaceTimeField) (S : ℝ) : Prop :=
  ∀ K : ℝ≥0∞, K ≠ ⊤ → ∃ δ : ℝ, 0 < δ ∧
    ∀ t₀ ∈ Icc (0 : ℝ) (S + 1), ∀ a' : SpatialField, a' ∈ initialClassR →
      sobolevENorm 7 a' ≤ K → δ ≤ A01.localHorizon' ν a' (timeShift t₀ f)

example (ν : ℝ) (hν : 0 < ν) (f : SpaceTimeField) (hf : MemForceR f)
    (S : ℝ) (hS : 0 ≤ S) : RestartFixedForceWide ν f S := by
  intro K hK
  let B := ‖sobolevPath (C01.forcePath (S := S + 1) hf)
    (C01.forcePath_jetLp_continuous (S := S + 1) hf) 6‖
  refine ⟨A01.uniformHorizon ν (A01.datumRadiusConstant * K.toReal) B,
    A01.uniformHorizon_pos _ _ _, ?_⟩
  intro t₀ ht₀ a ha hbound
  rw [A01.localHorizon'_eq hν ha (restart_force f hf t₀ ht₀.1)]
  apply A01.uniformHorizon_antitone ν _
    (referenceForce_timeShift_norm_le f hf S t₀ ht₀)
  obtain ⟨D, hD⟩ := ha.1.2 7
  have hD' : D01.IsSobolevDatum 7 (A01.selectedDatum a ha).field D := by
    rw [(A01.selectedDatum_spec a ha).1]
    exact hD
  have hn : ‖D‖ ≤ K.toReal := by
    have h := ENNReal.toReal_mono hK hbound
    have he : sobolevENorm 7 a = ‖D‖ₑ := sobolevENorm_eq hD
    rw [he] at h
    simpa only [toReal_enorm] using h
  exact (A01.cylinderDatum_norm_le (A01.selectedDatum a ha) D hD').trans
    (mul_le_mul_of_nonneg_left hn A01.datumRadiusConstant_nonneg)

end NSFormalization.Section4.A04
