import NSFormalization.Section4.R44.Prop44

/-! Theorem 4.1(ii), the q = 2 non-density clause.
The threshold -1/2 is the zero of `ThresholdAPI.l2` in
`verification/Contracts/V1/Thresholds.lean`: exponent 2 s = -1/2 - s.
The force class and relative-density vocabulary are imported from NonDensityL1. -/
noncomputable section
namespace NSFormalization.Section4.R41
open A02 (SpaceTimeField)
open D01
open scoped ENNReal

/-- The same explicit Proposition 4.4 radius excludes breakdown at time T. -/
theorem radius_le_forceSobolevENorm_L2 {ν T s : ℝ} (hν : 0 < ν) (hT : 0 < T)
    (hs : -1 / 2 ≤ s) {f : SpaceTimeField} (hf : f ∈ breakdownSetRZero ν T) :
    ENNReal.ofReal (R44.radius ν T) ≤ forceSobolevENorm 2 s f := by
  have hhalf : ENNReal.ofReal (R44.radius ν T) ≤ forceSobolevENorm 2 (-1 / 2) f := by
    apply le_of_not_gt
    intro hsmall
    exact R44.nonDensityBallZero ν T hν hT f hf.1 hsmall hf
  exact hhalf.trans (forceSobolevENorm_mono_order 2 (-1 / 2) s hs f)

/-- RMainAPI.nonDensityZero at q = 2, with ρ = R44.radius ν T. -/
theorem nonDensityZero_L2 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ, -1 / 2 ≤ s →
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ f ∈ breakdownSetRZero ν T,
      ENNReal.ofReal ρ ≤ forceSobolevENorm 2 s f := by
  intro ν T hν hT s hs
  exact ⟨R44.radius ν T, R44.radius_pos hν,
    fun _ hf => radius_le_forceSobolevENorm_L2 hν hT hs hf⟩

/-- Theorem 4.1(ii), failure of relative density at and above the L² threshold. -/
theorem not_breakdownDenseR_zero_L2 : ∀ ν T : ℝ, 0 < ν → 0 < T → ∀ s : ℝ,
    -1 / 2 ≤ s → ¬ BreakdownDenseR ν (fun _ => 0) T 2 s := by
  intro ν T hν hT s hs hdense
  obtain ⟨ρ, hρ, hbound⟩ := nonDensityZero_L2 ν T hν hT s hs
  obtain ⟨f, hf, hdist⟩ := hdense 0 zero_mem_forceClassR (ENNReal.ofReal ρ)
    (ENNReal.ofReal_pos.mpr hρ)
  simp only [sub_zero] at hdist
  exact (not_lt_of_ge (hbound f hf)) hdist

example : (0 : SpaceTimeField) ∈ forceClassR := zero_mem_forceClassR
example : ¬ BreakdownDenseR 1 (fun _ => 0) 1 2 (-1 / 2) :=
  not_breakdownDenseR_zero_L2 1 1 (by norm_num) (by norm_num) _ le_rfl

end NSFormalization.Section4.R41
