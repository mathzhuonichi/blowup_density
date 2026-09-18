import NSFormalization.Section3.T11.LocalTheory
import NavierStokes.ResidualCalculus

/-!
# Positive-viscosity rescaling algebra

This module proves the two algebraic fields of the periodic viscosity-rescaling
API.  Constant positive rescaling preserves the initial-data class, while the
force's compact temporal support is carried from `K` to its image under
`t ↦ ν * t`.  The three restore-after-normalize identities are pointwise
positive-viscosity algebra.
-/

noncomputable section

namespace NSFormalization.Section3.T11

open Set
open NavierStokes.ProblemStatement
open NavierStokes.ResidualCalculus
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar IsSolenoidal)
open NSFormalization.Section3.T10
open scoped ContDiff

private lemma unitViscosityInitialT_mem_initialClassT
    {ν : ℝ} {a : SpatialField} (ha : a ∈ initialClassT) :
    unitViscosityInitialT ν a ∈ initialClassT := by
  rcases ha with ⟨ha_smooth, ha_periodic, ha_solenoidal⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ha_smooth.const_smul ν⁻¹
  · intro x i
    exact congrArg (ν⁻¹ • ·) (ha_periodic x i)
  · intro x
    change spatialDivergence
      (fun z : SpaceTime ↦ ν⁻¹ • a z.2) 0 x = 0
    rw [spatialDivergence_const_smul
      (fun z : SpaceTime ↦ a z.2) 0 x ν⁻¹
      (ha_smooth.differentiable (by simp) x), ha_solenoidal x, mul_zero]

private lemma unitViscosityForceT_mem_forceClassT
    {ν : ℝ} (hν : 0 < ν) {f : SpaceTimeField} (hf : f ∈ forceClassT) :
    unitViscosityForceT ν f ∈ forceClassT := by
  rcases hf with ⟨hf_smooth, hf_periodic, K, hK_compact, hK_pos, hf_support⟩
  let Kν : Set ℝ := (fun t : ℝ ↦ ν * t) '' K
  refine ⟨?_, ?_, Kν, ?_, ?_, ?_⟩
  · exact (hf_smooth.comp
      ((contDiff_fst.div_const ν).prodMk contDiff_snd)).const_smul (ν ^ 2)⁻¹
  · intro t _ht x i
    exact congrArg ((ν ^ 2)⁻¹ • ·)
      (hf_periodic (t / ν) (mem_univ _) x i)
  · exact hK_compact.image (continuous_const.mul continuous_id)
  · rintro _ ⟨t, ht, rfl⟩
    exact mul_pos hν (hK_pos ht)
  · apply closure_minimal _
      ((hK_compact.image (continuous_const.mul continuous_id)).isClosed.prod
        isClosed_univ)
    intro z hz
    have hf_ne : f (z.1 / ν, z.2) ≠ 0 := by
      intro hf_zero
      exact hz (by simp [unitViscosityForceT, hf_zero])
    have hs : (z.1 / ν, z.2) ∈ tsupport f := subset_tsupport f hf_ne
    refine ⟨⟨z.1 / ν, (hf_support hs).1, ?_⟩, mem_univ _⟩
    change ν * (z.1 / ν) = z.1
    field_simp [ne_of_gt hν]

/-- Positive-viscosity rescaling preserves the canonical periodic initial and
force classes. -/
theorem scaled_classes : ∀ (ν : ℝ), 0 < ν →
    ∀ (a : SpatialField), a ∈ initialClassT →
      ∀ (f : SpaceTimeField), f ∈ forceClassT →
        unitViscosityInitialT ν a ∈ initialClassT ∧
          unitViscosityForceT ν f ∈ forceClassT := by
  intro ν hν a ha f hf
  exact ⟨unitViscosityInitialT_mem_initialClassT ha,
    unitViscosityForceT_mem_forceClassT hν hf⟩

/-- Restoring viscosity after unit-viscosity normalization recovers all three
physical fields exactly. -/
theorem inverse_identities : ∀ (ν : ℝ), 0 < ν →
    ∀ (u : SpaceTimeField) (p : SpaceTimeScalar) (f : SpaceTimeField),
      restoreViscosityVelocityT ν (unitViscosityVelocityT ν u) = u ∧
        restoreViscosityPressureT ν (unitViscosityPressureT ν p) = p ∧
        restoreViscosityForceT ν (unitViscosityForceT ν f) = f := by
  intro ν hν u p f
  have hν0 : ν ≠ 0 := ne_of_gt hν
  constructor
  · funext z
    simp [restoreViscosityVelocityT, unitViscosityVelocityT,
      smul_smul, hν0]
  constructor
  · funext z
    simp [restoreViscosityPressureT, unitViscosityPressureT, hν0]
  · funext z
    simp [restoreViscosityForceT, unitViscosityForceT, smul_smul, hν0]

end NSFormalization.Section3.T11
