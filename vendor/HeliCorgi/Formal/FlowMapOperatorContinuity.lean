import Mathlib
import Formal.FlowMapChainRule

namespace MNS2

open Set
open scoped Interval

/--
Evaluation at a fixed direction is continuous on the space of continuous linear maps.

Hence, if `J(s)` varies continuously in operator norm, then the tangent action
`s ↦ J(s) d` is continuous for every fixed direction `d`.
-/
theorem continuousOn_clm_apply_fixed
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (J : ℝ → (X →L[ℝ] Y)) (d : X)
    (hJ : ContinuousOn J (uIcc (0 : ℝ) 1)) :
    ContinuousOn (fun s : ℝ => J s d) (uIcc (0 : ℝ) 1) := by
  exact
    (isBoundedBilinearMap_apply (𝕜 := ℝ)).continuous_left.comp_continuousOn hJ

/--
Affine flow-map bridge with continuity assumed at the operator level.

Compared with `affine_flowmap_bridge_of_fderiv`, this theorem no longer asks separately
for continuity of the scalar-path tangent `J(s) d`: continuity of the operator-valued
Fréchet derivative family `J` implies it automatically by continuous evaluation.
-/
theorem affine_flowmap_bridge_of_fderiv_continuous_operator
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (x d : X) (J : ℝ → (X →L[ℝ] Y))
    (hS : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasFDerivAt S (J s) (x + s • d))
    (hJ : ContinuousOn J (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, J s d) = S (x + d) - S x := by
  apply affine_flowmap_bridge_of_fderiv
    (S := S) (x := x) (d := d) (J := J) hS
  exact continuousOn_clm_apply_fixed J d hJ

/--
Radial amplitude-path specialization with operator-level continuity.
-/
theorem radial_flowmap_bridge_of_fderiv_continuous_operator
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (d : X) (J : ℝ → (X →L[ℝ] Y))
    (hS : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasFDerivAt S (J s) (s • d))
    (hJ : ContinuousOn J (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, J s d) = S d - S 0 := by
  have hS' : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasFDerivAt S (J s) ((0 : X) + s • d) := by
    simpa using hS
  simpa using
    (affine_flowmap_bridge_of_fderiv_continuous_operator
      (S := S) (x := (0 : X)) (d := d) (J := J) hS' hJ)

end MNS2
