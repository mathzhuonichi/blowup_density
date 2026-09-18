import NSFormalization.Section3.T20.CriticalRegularity
import NavierStokes.PeriodicUniqueness

/-!
# T20 unit U4 — `constantTransportSkew` (`03-torus.tex:411`)

This module proves the reconciled `CriticalRegularityTAPI.constantTransportSkew`
field verbatim: for smooth periodic `v, w` on the unit three-torus and any fixed
`m : Space`, the constant-coefficient first-order transport `(m·∇)` is
skew-adjoint on `L²(T³)`:
`⟪(m·∇)v, w⟫_{L²(T³)} = -⟪v, (m·∇)w⟫`.

The pairing `periodicPairing` over the probability torus equals the physical
unit-cube integral (`NSFormalization.Paper1.integral_torusLift`).  Writing the
constant transport as the coordinate sum `(m·∇)v = ∑ⱼ mⱼ ∂ⱼ v` (Fréchet
derivative in the constant direction `m`) reduces the identity to the
per-direction vector integration by parts
`NavierStokes.PeriodicUniqueness.cubeIntegral_inner_partial`, which is derived
from Mathlib's divergence theorem on the cube.  The two `Integrable` premises
the manuscript field carries are unused here: the cube-integral identity holds
regardless, so they only protect the Bochner integral in the statement.
-/

noncomputable section

namespace NSFormalization.Section3.T20

open Set MeasureTheory
open NavierStokes.ProblemStatement
open NavierStokes.PeriodicIntegration
open NavierStokes.PeriodicUniqueness
open NSFormalization.Section4.A02
  (SpatialField SpaceTimeField SpaceTimeScalar forceTimeMeasure)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T11
open NSFormalization.Section3.T12
open scoped ContDiff ENNReal BigOperators InnerProductSpace

/-- The periodic `L²` pairing is the physical unit-cube integral of the pointwise
Euclidean inner product. -/
private theorem periodicPairing_eq_cubeIntegral (a b : SpatialField) :
    periodicPairing a b = cubeIntegral (fun x => (inner ℝ (a x) (b x) : ℝ)) := by
  unfold periodicPairing
  exact NSFormalization.Paper1.integral_torusLift (fun x => (inner ℝ (a x) (b x) : ℝ))

/-- The fixed-time constant transport is the coordinate sum of directional
partials `(m·∇)v = ∑ⱼ mⱼ ∂ⱼ v`. -/
private theorem constantTransportSpatialT_eq_sum (m : Space) (v : SpatialField) (x : Space) :
    constantTransportSpatialT m v x = ∑ i : Fin 3, m i • spatialPartial i v x := by
  have h1 : constantTransportSpatialT m v x = fderiv ℝ v x m := rfl
  rw [h1]
  conv_lhs => rw [← sum_coordinates m]
  simp only [map_sum, map_smul]
  rfl

/-- `03-torus.tex:411`: for smooth periodic `v, w` the constant transport
`(m·∇)` is skew-adjoint on `L²(T³)`. -/
theorem constantTransportSkew : ∀ (m : Space) (v w : SpatialField),
    SmoothPeriodicT v → SmoothPeriodicT w →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift (constantTransportSpatialT m v) y)
            (torusLift w y) : ℝ)) periodicTorusMeasure →
      Integrable
        (fun y : PeriodicTorus ↦
          (inner ℝ (torusLift v y)
            (torusLift (constantTransportSpatialT m w) y) : ℝ))
        periodicTorusMeasure →
        periodicPairing (constantTransportSpatialT m v) w =
          -periodicPairing v (constantTransportSpatialT m w) := by
  intro m v w hv hw _ _
  obtain ⟨hvc, hvp⟩ := hv
  obtain ⟨hwc, hwp⟩ := hw
  -- per-direction integration by parts, oriented as ∫⟪∂ᵢv, w⟫ = -∫⟪v, ∂ᵢw⟫
  have key : ∀ i : Fin 3,
      cubeIntegral (fun x => (inner ℝ (spatialPartial i v x) (w x) : ℝ)) =
        -cubeIntegral (fun x => (inner ℝ (v x) (spatialPartial i w x) : ℝ)) := by
    intro i
    have h := cubeIntegral_inner_partial hvc hwc hvp hwp i
    linarith [h]
  have hcont1 : ∀ i : Fin 3,
      Continuous (fun x => (inner ℝ (spatialPartial i v x) (w x) : ℝ)) :=
    fun i => ((spatial_partial_contDiff hvc i).inner ℝ hwc).continuous
  have hcont2 : ∀ i : Fin 3,
      Continuous (fun x => (inner ℝ (v x) (spatialPartial i w x) : ℝ)) :=
    fun i => (hvc.inner ℝ (spatial_partial_contDiff hwc i)).continuous
  -- expand the left pairing over the coordinate sum
  have hLHS : cubeIntegral (fun x =>
        (inner ℝ (constantTransportSpatialT m v x) (w x) : ℝ)) =
      ∑ i : Fin 3, m i *
        cubeIntegral (fun x => (inner ℝ (spatialPartial i v x) (w x) : ℝ)) := by
    have hfun : (fun x => (inner ℝ (constantTransportSpatialT m v x) (w x) : ℝ)) =
        (fun x => ∑ i : Fin 3, m i * (inner ℝ (spatialPartial i v x) (w x) : ℝ)) := by
      funext x
      rw [constantTransportSpatialT_eq_sum, sum_inner]
      exact Finset.sum_congr rfl (fun i _ => real_inner_smul_left _ _ _)
    rw [hfun]
    have hsum := cubeIntegral_sum (ι := Fin 3) Finset.univ
      (fun i x => m i * (inner ℝ (spatialPartial i v x) (w x) : ℝ))
      (fun i _ => continuous_const.mul (hcont1 i))
    rw [hsum]
    exact Finset.sum_congr rfl (fun i _ => cubeIntegral_const_mul _ _)
  -- expand the right pairing over the coordinate sum
  have hRHS : cubeIntegral (fun x =>
        (inner ℝ (v x) (constantTransportSpatialT m w x) : ℝ)) =
      ∑ i : Fin 3, m i *
        cubeIntegral (fun x => (inner ℝ (v x) (spatialPartial i w x) : ℝ)) := by
    have hfun : (fun x => (inner ℝ (v x) (constantTransportSpatialT m w x) : ℝ)) =
        (fun x => ∑ i : Fin 3, m i * (inner ℝ (v x) (spatialPartial i w x) : ℝ)) := by
      funext x
      rw [constantTransportSpatialT_eq_sum, inner_sum]
      exact Finset.sum_congr rfl (fun i _ => real_inner_smul_right _ _ _)
    rw [hfun]
    have hsum := cubeIntegral_sum (ι := Fin 3) Finset.univ
      (fun i x => m i * (inner ℝ (v x) (spatialPartial i w x) : ℝ))
      (fun i _ => continuous_const.mul (hcont2 i))
    rw [hsum]
    exact Finset.sum_congr rfl (fun i _ => cubeIntegral_const_mul _ _)
  rw [periodicPairing_eq_cubeIntegral, periodicPairing_eq_cubeIntegral, hLHS, hRHS,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [key i]
  ring

end NSFormalization.Section3.T20
