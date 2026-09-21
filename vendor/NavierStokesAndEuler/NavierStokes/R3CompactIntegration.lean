import NavierStokes.ComparatorBridge
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Whole-space integration with compactly supported test fields

The integrals here are Lebesgue integrals over Euclidean three-space. Boundary
terms vanish because the test field has compact support. The other field,
including the pressure, need not be periodic or compactly supported.
-/

noncomputable section

namespace NavierStokes.R3CompactIntegration

open Set MeasureTheory InnerProductSpace ProblemStatement
open scoped ContDiff RealInnerProductSpace

def spatialPartial (i : Fin 3) (f : Space → ℝ) (x : Space) : ℝ :=
  fderiv ℝ f x (coordinateVector i)

theorem partial_continuous {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (spatialPartial i f) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem partial_compact {f : Space → ℝ} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (spatialPartial i f) := hf.fderiv_apply ℝ (coordinateVector i)

theorem integrable_mul {f g : Space → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hs : HasCompactSupport f) : Integrable (fun x => f x * g x) :=
  (hf.mul hg).integrable_of_hasCompactSupport hs.mul_right

theorem integration_by_parts {f g : Space → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport f) (i : Fin 3) :
    (∫ x : Space, f x * spatialPartial i g x) = -(∫ x : Space, spatialPartial i f x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul (partial_continuous hf i) hg.continuous (partial_compact hs i)
  · exact integrable_mul hf.continuous (partial_continuous hg i) hs
  · exact integrable_mul hf.continuous hg.continuous hs
  · intro x _
    exact hf.differentiable (by norm_num) x
  · intro x _
    exact hg.differentiable (by norm_num) x

theorem component_contDiff {u : Space → Space} (hu : ContDiff ℝ 1 u) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => u x i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hu

theorem component_compact {u : Space → Space} (hu : HasCompactSupport u) (i : Fin 3) :
    HasCompactSupport (fun x => u x i) := by
  apply hu.mono'
  intro x hx
  by_contra hxu
  exact hx (by
    change u x i = 0
    rw [image_eq_zero_of_notMem_tsupport hxu]
    rfl)

theorem partial_component {u : Space → Space} (hu : ContDiff ℝ 1 u)
    (i j : Fin 3) (x : Space) :
    spatialPartial i (fun y => u y j) x = (fderiv ℝ u x (coordinateVector i)) j := by
  unfold spatialPartial
  change (fderiv ℝ ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) ∘ u) x)
    (coordinateVector i) = _
  rw [((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x
    (hu.differentiable (by norm_num) x).hasFDerivAt).fderiv]
  rfl

/-- The compact test velocity kills the pressure term on all of `ℝ³`. -/
theorem integral_inner_gradient_eq_zero {u : Space → Space} {p : Space → ℝ}
    (hu : ContDiff ℝ 1 u) (hp : ContDiff ℝ 1 p) (hs : HasCompactSupport u)
    (hd : ∀ x : Space, Comparator.divergence u x = 0) :
    (∫ x : Space, ⟪u x, gradient p x⟫_ℝ) = 0 := by
  have hinner (x : Space) : ⟪u x, gradient p x⟫_ℝ =
      ∑ i : Fin 3, u x i * spatialPartial i p x := by
    rw [← ComparatorBridge.gradient_eq (fun z => p z.2) 0 x]
    simp [pressureGradient, spatialPartial, coordinateVector, inner_sum, inner_smul_right,
      EuclideanSpace.inner_single_right, mul_comm]
  have hleft (i : Fin 3) : Integrable (fun x : Space => u x i * spatialPartial i p x) :=
    integrable_mul (component_contDiff hu i).continuous (partial_continuous hp i)
      (component_compact hs i)
  have hright (i : Fin 3) :
      Integrable (fun x : Space => spatialPartial i (fun y => u y i) x * p x) :=
    integrable_mul (partial_continuous (component_contDiff hu i) i) hp.continuous
      (partial_compact (component_compact hs i) i)
  calc
    (∫ x : Space, ⟪u x, gradient p x⟫_ℝ) =
        ∑ i : Fin 3, ∫ x : Space, u x i * spatialPartial i p x := by
      simp_rw [hinner]
      exact integral_finsetSum _ (fun i _ => hleft i)
    _ = ∑ i : Fin 3, -(∫ x : Space, spatialPartial i (fun y => u y i) x * p x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact integration_by_parts (component_contDiff hu i) hp (component_compact hs i) i
    _ = -(∫ x : Space, (∑ i : Fin 3, spatialPartial i (fun y => u y i) x) * p x) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      simp_rw [Finset.sum_mul]
      exact (integral_finsetSum _ (fun i _ => hright i)).symm
    _ = 0 := by
      have hsum (x : Space) : (∑ i : Fin 3, spatialPartial i (fun y => u y i) x) = 0 := by
        simp_rw [partial_component hu]
        exact (ComparatorBridge.divergence_eq (fun z => u z.2) 0 x).trans (hd x)
      simp [hsum]

end NavierStokes.R3CompactIntegration
