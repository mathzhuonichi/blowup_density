import Mathlib
import Formal.FlowMapOperatorContinuity

namespace MNS2

open Set
open scoped Interval ContDiff

/--
A globally `C¹` map satisfies the affine flow-map path-integral identity with its
canonical Fréchet derivative `fderiv`.

This removes the externally supplied derivative family `J`: differentiability of `S`
and operator-norm continuity of `fderiv ℝ S` are both consequences of `ContDiff ℝ 1 S`.
-/
theorem affine_flowmap_bridge_of_contDiff_one
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (x d : X)
    (hS : ContDiff ℝ 1 S) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ S (x + s • d)) d) =
      S (x + d) - S x := by
  apply affine_flowmap_bridge_of_fderiv_continuous_operator
    (S := S) (x := x) (d := d)
    (J := fun s : ℝ => fderiv ℝ S (x + s • d))
  · intro s _hs
    exact (hS.differentiable_one (x + s • d)).hasFDerivAt
  · have hfderiv : Continuous (fderiv ℝ S) :=
      hS.continuous_fderiv one_ne_zero
    have hpath : Continuous (fun s : ℝ => x + s • d) := by
      fun_prop
    exact (hfderiv.comp hpath).continuousOn

/--
Radial amplitude-path specialization of the `C¹` bridge.

For the path `s ↦ s • d`, the tangent direction remains the fixed, unnormalized
vector `d`, and the exact integrand is `(fderiv ℝ S (s • d)) d`.
-/
theorem radial_flowmap_bridge_of_contDiff_one
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (d : X)
    (hS : ContDiff ℝ 1 S) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ S (s • d)) d) =
      S d - S 0 := by
  simpa using
    (affine_flowmap_bridge_of_contDiff_one
      (S := S) (x := (0 : X)) (d := d) hS)

end MNS2
