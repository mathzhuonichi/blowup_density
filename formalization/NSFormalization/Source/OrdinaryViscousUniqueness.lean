import NSFormalization.Source.OrdinaryViscousStability
import NSFormalization.Source.SobolevSlabBounds

/-! Actual forced whole-space PDE uniqueness on a closed slab. This is a
uniqueness component of Paper 3 local theory, not a local existence theorem. -/
noncomputable section
namespace NSFormalization.Source.OrdinaryViscousUniqueness
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
  EulerOrdinarySobolev OrdinaryViscousStability
open scoped ContDiff

/-- Only the pressure gradient is an L2 field; its potential need not be L2. -/
def pressureResidual (ν : ℝ) (U D F : SmoothL2Field Space) : SmoothL2Field Space :=
  addField (fieldSub (fieldSub F D) (advectionField U U))
    (mapField (ν • ContinuousLinearMap.id ℝ Space) (laplacianField U))

theorem pressureResidual_field (ν : ℝ) (U D F : SmoothL2Field Space) (x : Space) :
    (pressureResidual ν U D F).field x = F.field x - D.field x -
      fderiv ℝ U.field x (U.field x) + ν • Laplacian.laplacian U.field x := by
  simp [pressureResidual, addField_field, fieldSub_field, advectionField_field,
    mapField_field, laplacianField_field]

/-- Equal initial data and common force give equal velocities. Uniform spatial
bounds and closed gradient-space membership are conclusions of the proof. -/
theorem velocity_unique {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 ≤ ν)
    (U₁ U₂ D₁ D₂ F : Icc (0 : ℝ) T → SmoothL2Field Space)
    (p₁ p₂ : Icc (0 : ℝ) T → Space → ℝ)
    (hU₁ : ∀ n, Continuous (fun t => (U₁ t).jetLp n))
    (hU₂ : ∀ n, Continuous (fun t => (U₂ t).jetLp n))
    (hD₁ : ∀ n, Continuous (fun t => (D₁ t).jetLp n))
    (hD₂ : ∀ n, Continuous (fun t => (D₂ t).jetLp n))
    (ht₁ : ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r => (U₁ (projIcc 0 T hT r)).field x)
        ((D₁ ⟨t, ht.1.le, ht.2.le⟩).field x) t)
    (ht₂ : ∀ t (ht : t ∈ Ioo 0 T) x,
      HasDerivAt (fun r => (U₂ (projIcc 0 T hT r)).field x)
        ((D₂ ⟨t, ht.1.le, ht.2.le⟩).field x) t)
    (hp₁ : ∀ t, ContDiff ℝ ∞ (p₁ t)) (hp₂ : ∀ t, ContDiff ℝ ∞ (p₂ t))
    (hdiv₁ : ∀ t x, divergence (U₁ t).field x = 0)
    (hdiv₂ : ∀ t x, divergence (U₂ t).field x = 0)
    (he₁ : ∀ t x, (D₁ t).field x + fderiv ℝ (U₁ t).field x ((U₁ t).field x) -
      ν • Laplacian.laplacian (U₁ t).field x + gradient (p₁ t) x = (F t).field x)
    (he₂ : ∀ t x, (D₂ t).field x + fderiv ℝ (U₂ t).field x ((U₂ t).field x) -
      ν • Laplacian.laplacian (U₂ t).field x + gradient (p₂ t) x = (F t).field x)
    (hzero : ∀ x, (U₁ ⟨0, le_rfl, hT⟩).field x = (U₂ ⟨0, le_rfl, hT⟩).field x) :
    ∀ t x, (U₁ t).field x = (U₂ t).field x := by
  let W := fun t => fieldSub (U₂ t) (U₁ t)
  let D := fun t => fieldSub (D₂ t) (D₁ t)
  let B₁ := fun t => pressureResidual ν (U₁ t) (D₁ t) (F t)
  let B₂ := fun t => pressureResidual ν (U₂ t) (D₂ t) (F t)
  let P := fun t => fieldSub (B₂ t) (B₁ t)
  have hg₁ t : (B₁ t).toLp ∈ gradientSpace := by
    apply gradient_mem _ (p₁ t) (hp₁ t)
    intro x
    dsimp [B₁]
    rw [pressureResidual_field, ← he₁ t x]
    abel
  have hg₂ t : (B₂ t).toLp ∈ gradientSpace := by
    apply gradient_mem _ (p₂ t) (hp₂ t)
    intro x
    dsimp [B₂]
    rw [pressureResidual_field, ← he₂ t x]
    abel
  obtain ⟨K, _, hK⟩ := SobolevSlabBounds.exists_uniform_derivative_bound U₁ hU₁
  have hwfield t : (W t).field = (U₂ t).field - (U₁ t).field :=
    funext (fieldSub_field _ _)
  have hsum t : (addField (U₁ t) (W t)).field = (U₂ t).field := by
    funext x
    simp only [addField_field, W, fieldSub_field]
    abel
  have hz := difference_zero hT hν U₁ W P D
    (continuous_jet_fieldSub U₂ U₁ hU₂ hU₁)
    (continuous_jet_fieldSub D₂ D₁ hD₂ hD₁)
    (by
      intro t ht x
      dsimp only [W, D]
      simp only [fieldSub_field]
      convert (ht₂ t ht x).sub (ht₁ t ht x) using 1 <;> rfl)
    K hK (by intro t x; rw [hsum]; exact hdiv₂ t x)
    (by
      intro t
      dsimp only [W]
      rw [toLp_fieldSub]
      exact solenoidalSpace.sub_mem
        (smooth_mem_solenoidal _ (U₂ t).smooth (U₂ t).memLp (hdiv₂ t))
        (smooth_mem_solenoidal _ (U₁ t).smooth (U₁ t).memLp (hdiv₁ t)))
    (by intro t; dsimp only [P]; rw [toLp_fieldSub]; exact gradientSpace.sub_mem (hg₂ t) (hg₁ t))
    (by
      intro t x
      rw [differenceRhs_field, laplacianField_field, hwfield]
      rw [fderiv_sub ((U₂ t).smooth.differentiable (by simp) x)
        ((U₁ t).smooth.differentiable (by simp) x)]
      rw [(show ContDiff ℝ 2 (U₂ t).field from (U₂ t).smooth.of_le (by simp)).contDiffAt.laplacian_sub
        (show ContDiff ℝ 2 (U₁ t).field from (U₁ t).smooth.of_le (by simp)).contDiffAt]
      simp only [D, P, B₁, B₂, fieldSub_field, pressureResidual_field,
        Pi.sub_apply, sub_apply, map_sub, smul_sub]
      abel_nf)
    (by funext x; simp only [W, fieldSub_field, Pi.zero_apply, hzero, sub_self])
  intro t x
  have h := congrFun (hz t) x
  simp only [W, fieldSub_field, Pi.zero_apply] at h
  exact (sub_eq_zero.mp h).symm

end NSFormalization.Source.OrdinaryViscousUniqueness
