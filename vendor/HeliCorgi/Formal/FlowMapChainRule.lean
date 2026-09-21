import Mathlib
import Formal.FlowMapFTC

namespace MNS2

open Set
open scoped Interval

/--
The affine initial-data path `t ↦ x + t • d` has derivative exactly `d`.

This records the unnormalized tangent-direction convention used by the flow-map bridge:
when the path parameter runs over `[0,1]`, the path derivative is `d`, not a normalized
version of `d` and not `t • d`.
-/
theorem affine_path_hasDerivAt
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (x d : X) (s : ℝ) :
    HasDerivAt (fun t : ℝ => x + t • d) d s := by
  simpa only [id, one_smul] using
    (((hasDerivAt_id s).smul_const d).const_add x)

/--
Flow-map bridge with the path derivative generated from a Fréchet derivative by the chain rule.

If `J s` is the Fréchet derivative of `S` at the point `x + s • d`, then the scalar-path
integrand is forced to be `J s d`. Under continuity of that tangent action, the interval
integral exactly reconstructs the endpoint increment.
-/
theorem affine_flowmap_bridge_of_fderiv
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (x d : X) (J : ℝ → (X →L[ℝ] Y))
    (hS : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasFDerivAt S (J s) (x + s • d))
    (hcont : ContinuousOn (fun s : ℝ => J s d) (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, J s d) = S (x + d) - S x := by
  apply affine_flowmap_bridge
    (S := S) (x := x) (d := d) (G := fun s : ℝ => J s d)
  · intro s hs
    have hpath : HasDerivAt (fun t : ℝ => x + t • d) d s :=
      affine_path_hasDerivAt x d s
    have hchain := (hS s hs).comp_hasDerivAt s hpath
    simpa [Function.comp_def] using hchain
  · exact hcont

/--
Radial specialization of `affine_flowmap_bridge_of_fderiv`.

For the amplitude path `s ↦ s • d`, the exact tangent integrand is `J s d` whenever
`J s = DS(s • d)` in the Fréchet sense.
-/
theorem radial_flowmap_bridge_of_fderiv
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (d : X) (J : ℝ → (X →L[ℝ] Y))
    (hS : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasFDerivAt S (J s) (s • d))
    (hcont : ContinuousOn (fun s : ℝ => J s d) (uIcc (0 : ℝ) 1)) :
    (∫ s in (0 : ℝ)..1, J s d) = S d - S 0 := by
  have hS' : ∀ s ∈ uIcc (0 : ℝ) 1,
      HasFDerivAt S (J s) ((0 : X) + s • d) := by
    simpa using hS
  simpa using
    (affine_flowmap_bridge_of_fderiv
      (S := S) (x := (0 : X)) (d := d) (J := J) hS' hcont)

end MNS2
