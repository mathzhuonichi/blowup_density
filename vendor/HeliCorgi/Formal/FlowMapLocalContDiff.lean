import Mathlib
import Formal.FlowMapContDiffOne

namespace MNS2

open Set
open scoped Interval ContDiff

/--
Local open-domain version of the affine `C¹` flow-map bridge.

This is the form needed for a local solution map: `S` need not be `C¹` on the whole
ambient Banach space. It is enough that `S` is `C¹` on an open set `U` containing the
entire affine path `s ↦ x + s • d` for `s ∈ [0,1]`.

The path tangent is still the fixed, unnormalized direction `d`.
-/
theorem affine_flowmap_bridge_of_contDiffOn_open
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (U : Set X) (hU : IsOpen U) (x d : X)
    (hS : ContDiffOn ℝ 1 S U)
    (hpath : MapsTo (fun s : ℝ => x + s • d) (uIcc (0 : ℝ) 1) U) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ S (x + s • d)) d) =
      S (x + d) - S x := by
  apply affine_flowmap_bridge_of_fderiv_continuous_operator
    (S := S) (x := x) (d := d)
    (J := fun s : ℝ => fderiv ℝ S (x + s • d))
  · intro s hs
    have hsU : x + s • d ∈ U := hpath hs
    have hSat : ContDiffAt ℝ 1 S (x + s • d) :=
      hS.contDiffAt (hU.mem_nhds hsU)
    exact (hSat.differentiableAt one_ne_zero).hasFDerivAt
  · have hfderiv : ContinuousOn (fderiv ℝ S) U :=
      hS.continuousOn_fderiv_of_isOpen hU (by norm_num)
    have hpath_cont : ContinuousOn (fun s : ℝ => x + s • d) (uIcc (0 : ℝ) 1) := by
      fun_prop
    exact hfderiv.comp hpath_cont hpath

/--
Local open-domain radial amplitude-path specialization.

For a solution map that is only known to be `C¹` on an open admissible-data set `U`,
it is enough to verify that the radial path `s ↦ s • d` remains inside `U`.
-/
theorem radial_flowmap_bridge_of_contDiffOn_open
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (S : X → Y) (U : Set X) (hU : IsOpen U) (d : X)
    (hS : ContDiffOn ℝ 1 S U)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) U) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ S (s • d)) d) =
      S d - S 0 := by
  have hpath' : MapsTo (fun s : ℝ => (0 : X) + s • d) (uIcc (0 : ℝ) 1) U := by
    simpa using hpath
  simpa using
    (affine_flowmap_bridge_of_contDiffOn_open
      (S := S) (U := U) hU (x := (0 : X)) (d := d) hS hpath')

end MNS2
