import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.Extend
import Formal.R3SchwartzConvectionSobolevEstimate
import Formal.R3SchwartzSobolevDensity

namespace MNS2

open scoped SchwartzMap

noncomputable section

/-- Schwartz convection is complex-linear in its first input as well as its bundled second input. -/
theorem r3SchwartzConvection_add_left
    (u₁ u₂ v : R3SchwartzVelocity) :
    r3SchwartzConvection (u₁ + u₂) v =
      r3SchwartzConvection u₁ v + r3SchwartzConvection u₂ v := by
  ext x j
  simp [r3SchwartzConvection_apply, add_smul, Finset.sum_add_distrib]

theorem r3SchwartzConvection_smul_left
    (c : ℂ) (u v : R3SchwartzVelocity) :
    r3SchwartzConvection (c • u) v = c • r3SchwartzConvection u v := by
  ext x j
  simp [r3SchwartzConvection_apply, Finset.smul_sum, smul_smul]

/--
The physical Schwartz convection term, viewed algebraically as a complex-bilinear map whose output
is the order-two Bessel coordinate.  Continuity here is deliberately measured later through the
order-three coordinate norms, not through the stronger Schwartz topology.
-/
def r3SchwartzConvectionHsCoreLinearMap :
    R3SchwartzVelocity →ₗ[ℂ] R3SchwartzVelocity →ₗ[ℂ] R3HsVelocity 2 :=
  LinearMap.mk₂ ℂ
    (fun u v => r3SchwartzToHsCLM 2 (r3SchwartzConvection u v))
    (by
      intro u₁ u₂ v
      rw [r3SchwartzConvection_add_left, map_add])
    (by
      intro c u v
      rw [r3SchwartzConvection_smul_left, map_smul])
    (by
      intro u v₁ v₂
      rw [map_add, map_add])
    (by
      intro c u v
      rw [map_smul, map_smul])

@[simp]
theorem r3SchwartzConvectionHsCoreLinearMap_apply
    (u v : R3SchwartzVelocity) :
    r3SchwartzConvectionHsCoreLinearMap u v =
      r3SchwartzToHsCLM 2 (r3SchwartzConvection u v) := by
  rfl

/-- Extend the second Schwartz input to the complete order-three Bessel-coordinate carrier. -/
def r3SchwartzConvectionRightExtension (u : R3SchwartzVelocity) :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 2 :=
  (r3SchwartzConvectionHsCoreLinearMap u).extendOfNorm
    (r3SchwartzToHsCLM 3).toLinearMap

@[simp]
theorem r3SchwartzConvectionRightExtension_apply_schwartz
    (u v : R3SchwartzVelocity) :
    r3SchwartzConvectionRightExtension u (r3SchwartzToHsCLM 3 v) =
      r3SchwartzToHsCLM 2 (r3SchwartzConvection u v) := by
  unfold r3SchwartzConvectionRightExtension
  apply LinearMap.extendOfNorm_eq (r3SchwartzToHsCLM_denseRange 3)
  refine ⟨r3SchwartzConvectionFullH3Constant * ‖r3SchwartzToHsCLM 3 u‖, ?_⟩
  intro w
  exact norm_r3SchwartzToHsCLM_two_convection_le_H3 u w

/-- Operator-norm bound for the extension in the second input. -/
theorem norm_r3SchwartzConvectionRightExtension_le
    (u : R3SchwartzVelocity) :
    ‖r3SchwartzConvectionRightExtension u‖ ≤
      r3SchwartzConvectionFullH3Constant * ‖r3SchwartzToHsCLM 3 u‖ := by
  unfold r3SchwartzConvectionRightExtension
  apply LinearMap.opNorm_extendOfNorm_le (r3SchwartzToHsCLM_denseRange 3)
    (mul_nonneg r3SchwartzConvectionFullH3Constant_nonneg (norm_nonneg _))
  intro v
  exact norm_r3SchwartzToHsCLM_two_convection_le_H3 u v

/-- The second-input extensions still depend complex-linearly on the first Schwartz input. -/
def r3SchwartzConvectionRightExtensionLinearMap :
    R3SchwartzVelocity →ₗ[ℂ] (R3HsVelocity 3 →L[ℂ] R3HsVelocity 2) where
  toFun := r3SchwartzConvectionRightExtension
  map_add' u₁ u₂ := by
    apply ContinuousLinearMap.ext
    intro x
    refine (r3SchwartzToHsCLM_denseRange 3).induction_on x ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro v
      change
        r3SchwartzConvectionRightExtension (u₁ + u₂) (r3SchwartzToHsCLM 3 v) =
          r3SchwartzConvectionRightExtension u₁ (r3SchwartzToHsCLM 3 v) +
            r3SchwartzConvectionRightExtension u₂ (r3SchwartzToHsCLM 3 v)
      rw [r3SchwartzConvectionRightExtension_apply_schwartz,
        r3SchwartzConvectionRightExtension_apply_schwartz,
        r3SchwartzConvectionRightExtension_apply_schwartz]
      change
        r3SchwartzConvectionHsCoreLinearMap (u₁ + u₂) v =
          r3SchwartzConvectionHsCoreLinearMap u₁ v +
            r3SchwartzConvectionHsCoreLinearMap u₂ v
      simpa using congrArg (fun f => f v)
        (r3SchwartzConvectionHsCoreLinearMap.map_add u₁ u₂)
  map_smul' c u := by
    apply ContinuousLinearMap.ext
    intro x
    refine (r3SchwartzToHsCLM_denseRange 3).induction_on x ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    · intro v
      change
        r3SchwartzConvectionRightExtension (c • u) (r3SchwartzToHsCLM 3 v) =
          c • r3SchwartzConvectionRightExtension u (r3SchwartzToHsCLM 3 v)
      rw [r3SchwartzConvectionRightExtension_apply_schwartz,
        r3SchwartzConvectionRightExtension_apply_schwartz]
      change
        r3SchwartzConvectionHsCoreLinearMap (c • u) v =
          c • r3SchwartzConvectionHsCoreLinearMap u v
      simpa using congrArg (fun f => f v)
        (r3SchwartzConvectionHsCoreLinearMap.map_smul c u)

@[simp]
theorem r3SchwartzConvectionRightExtensionLinearMap_apply
    (u : R3SchwartzVelocity) :
    r3SchwartzConvectionRightExtensionLinearMap u =
      r3SchwartzConvectionRightExtension u := by
  rfl

/--
The completed complex-bilinear convection map
`H³(R³; C³) × H³(R³; C³) → H²(R³; C³)` in Bessel coordinates.

The two Sobolev orders are written explicitly even though the current carrier implementation uses
the same underlying `L²` coordinate type: their physical meanings are fixed by the order-dependent
decoders and by the exact Schwartz agreement theorem below.
-/
def r3ConvectionH3ToH2 :
    R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 →L[ℂ] R3HsVelocity 2 :=
  r3SchwartzConvectionRightExtensionLinearMap.extendOfNorm
    (r3SchwartzToHsCLM 3).toLinearMap

@[simp]
theorem r3ConvectionH3ToH2_apply_schwartz_left
    (u : R3SchwartzVelocity) :
    r3ConvectionH3ToH2 (r3SchwartzToHsCLM 3 u) =
      r3SchwartzConvectionRightExtension u := by
  unfold r3ConvectionH3ToH2
  apply LinearMap.extendOfNorm_eq (r3SchwartzToHsCLM_denseRange 3)
  exact ⟨r3SchwartzConvectionFullH3Constant,
    norm_r3SchwartzConvectionRightExtension_le⟩

/-- The completed map agrees exactly with physical convection on canonical Schwartz coordinates. -/
@[simp]
theorem r3ConvectionH3ToH2_apply_schwartz
    (u v : R3SchwartzVelocity) :
    r3ConvectionH3ToH2
        (r3SchwartzToHsCLM 3 u) (r3SchwartzToHsCLM 3 v) =
      r3SchwartzToHsCLM 2 (r3SchwartzConvection u v) := by
  rw [r3ConvectionH3ToH2_apply_schwartz_left]
  exact r3SchwartzConvectionRightExtension_apply_schwartz u v

/-- On Schwartz inputs, decoding the order-two output recovers literal physical convection. -/
theorem r3HsToTempered_r3ConvectionH3ToH2_schwartz
    (u v : R3SchwartzVelocity) :
    r3HsToTemperedCLM 2
        (r3ConvectionH3ToH2
          (r3SchwartzToHsCLM 3 u) (r3SchwartzToHsCLM 3 v)) =
      (r3SchwartzConvection u v : 𝓢'(R3, R3C)) := by
  rw [r3ConvectionH3ToH2_apply_schwartz,
    r3HsToTempered_r3SchwartzToHsCLM]

/-- The completed bilinear operator has the same explicit bound as its Schwartz core. -/
theorem norm_r3ConvectionH3ToH2_le :
    ‖r3ConvectionH3ToH2‖ ≤ r3SchwartzConvectionFullH3Constant := by
  unfold r3ConvectionH3ToH2
  exact LinearMap.opNorm_extendOfNorm_le
    (r3SchwartzToHsCLM_denseRange 3)
    r3SchwartzConvectionFullH3Constant_nonneg
    norm_r3SchwartzConvectionRightExtension_le

/-- Pointwise `H³ × H³ → H²` norm estimate on the complete coordinate carriers. -/
theorem norm_r3ConvectionH3ToH2_apply_le
    (u v : R3HsVelocity 3) :
    ‖r3ConvectionH3ToH2 u v‖ ≤
      r3SchwartzConvectionFullH3Constant * ‖u‖ * ‖v‖ := by
  calc
    ‖r3ConvectionH3ToH2 u v‖ ≤ ‖r3ConvectionH3ToH2‖ * ‖u‖ * ‖v‖ :=
      r3ConvectionH3ToH2.le_opNorm₂ u v
    _ ≤ r3SchwartzConvectionFullH3Constant * ‖u‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right norm_r3ConvectionH3ToH2_le (norm_nonneg _))
        (norm_nonneg _)

/--
The completed convection map is the unique continuous complex-bilinear map with the stated
Schwartz-core values.
-/
theorem r3ConvectionH3ToH2_unique
    (B : R3HsVelocity 3 →L[ℂ] R3HsVelocity 3 →L[ℂ] R3HsVelocity 2)
    (hB : ∀ u v : R3SchwartzVelocity,
      B (r3SchwartzToHsCLM 3 u) (r3SchwartzToHsCLM 3 v) =
        r3SchwartzToHsCLM 2 (r3SchwartzConvection u v)) :
    B = r3ConvectionH3ToH2 := by
  apply ContinuousLinearMap.ext
  intro x
  refine (r3SchwartzToHsCLM_denseRange 3).induction_on x ?_ ?_
  · exact isClosed_eq B.continuous r3ConvectionH3ToH2.continuous
  · intro u
    apply ContinuousLinearMap.ext
    intro y
    refine (r3SchwartzToHsCLM_denseRange 3).induction_on y ?_ ?_
    · exact isClosed_eq
        (B (r3SchwartzToHsCLM 3 u)).continuous
        (r3ConvectionH3ToH2 (r3SchwartzToHsCLM 3 u)).continuous
    · intro v
      rw [hB u v, r3ConvectionH3ToH2_apply_schwartz]

end

end MNS2
