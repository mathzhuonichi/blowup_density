import Mathlib

namespace MNS2

open Set
open scoped Interval

/--
Fundamental path-integral bridge in a real Banach space.

If `G s` is the derivative of the endpoint map `F` all along the interval `[0,1]`
and `G` is continuous there, then integrating the tangent recovers the exact endpoint
increment `F 1 - F 0`.
-/
theorem path_integral_eq_endpoint_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F G : ℝ → E)
    (hderiv : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt F (G s) s)
    (hcont : ContinuousOn G (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, G s) = F 1 - F 0 := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable

/--
Affine initial-data path version of the bridge.

For `c(t) = x + t • d`, if `G(t)` is the derivative of `S ∘ c`, then its interval
integral exactly reconstructs `S (x + d) - S x`.
-/
theorem affine_flowmap_bridge
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (x d : X) (G : ℝ → Y)
    (hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => S (x + t • d)) (G s) s)
    (hcont : ContinuousOn G (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, G s) = S (x + d) - S x := by
  simpa using
    (path_integral_eq_endpoint_sub
      (F := fun t : ℝ => S (x + t • d)) (G := G) hderiv hcont)

/--
Radial path used by the amplitude bridge: `c(t) = t • d`.
This is the exact form behind `S(d) - S(0) = ∫ G(t) dt`.
-/
theorem radial_flowmap_bridge
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (d : X) (G : ℝ → Y)
    (hderiv : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => S (t • d)) (G s) s)
    (hcont : ContinuousOn G (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, G s) = S d - S 0 := by
  have hderiv' : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => S ((0 : X) + t • d)) (G s) s := by
    simpa using hderiv
  simpa using
    (affine_flowmap_bridge
      (S := S) (x := (0 : X)) (d := d) (G := G) hderiv' hcont)

end MNS2
