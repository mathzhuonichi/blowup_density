import Mathlib
import Formal.FlowMapLocalContDiff

namespace MNS2

open Set
open scoped Interval ContDiff

/--
A fixed-time PDE bridge adapter packages the analytic hypotheses needed by the
flow-map bridge together with an abstract semantic relation `EvolvesAt`.

`EvolvesAt x y` is intended to mean that `y` is the genuine PDE state at the
chosen time produced from initial datum `x`.  This structure does not define a
particular PDE and does not prove that such a relation is inhabited for
Navier–Stokes.  A PDE-specific layer must supply that meaning and prove the
`realizesPDE` field.
-/
structure FixedTimePDEBridgeAdapter
    (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (EvolvesAt : X → Y → Prop) where
  stateMap : X → Y
  admissible : Set X
  admissible_open : IsOpen admissible
  contDiffOn_stateMap : ContDiffOn ℝ 1 stateMap admissible
  realizesPDE : ∀ x ∈ admissible, EvolvesAt x (stateMap x)

section Adapter

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {EvolvesAt : X → Y → Prop}

/-- The entire affine initial-data path stays in the certified admissible domain. -/
def FixedTimePDEBridgeAdapter.AffinePathAdmissible
    (A : FixedTimePDEBridgeAdapter X Y EvolvesAt) (x d : X) : Prop :=
  MapsTo (fun s : ℝ => x + s • d) (uIcc (0 : ℝ) 1) A.admissible

/-- The entire radial amplitude path stays in the certified admissible domain. -/
def FixedTimePDEBridgeAdapter.RadialPathAdmissible
    (A : FixedTimePDEBridgeAdapter X Y EvolvesAt) (d : X) : Prop :=
  MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) A.admissible

/--
Every point on a certified affine path is mapped to a state satisfying the
abstract fixed-time PDE relation.
-/
theorem FixedTimePDEBridgeAdapter.affine_path_realizesPDE
    (A : FixedTimePDEBridgeAdapter X Y EvolvesAt) (x d : X)
    (hpath : A.AffinePathAdmissible x d)
    {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) 1) :
    EvolvesAt (x + s • d) (A.stateMap (x + s • d)) := by
  exact A.realizesPDE (x + s • d) (hpath hs)

/--
Exact affine bridge for a certified fixed-time PDE map.

The theorem uses only the analytic fields of the adapter.  The semantic field
`realizesPDE` is what permits a later PDE-specific layer to interpret the
endpoint map as an actual evolution map rather than an arbitrary `C¹` map.
-/
theorem FixedTimePDEBridgeAdapter.affine_bridge
    (A : FixedTimePDEBridgeAdapter X Y EvolvesAt) (x d : X)
    (hpath : A.AffinePathAdmissible x d) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ A.stateMap (x + s • d)) d) =
      A.stateMap (x + d) - A.stateMap x := by
  exact
    affine_flowmap_bridge_of_contDiffOn_open
      (S := A.stateMap) (U := A.admissible) A.admissible_open
      (x := x) (d := d) A.contDiffOn_stateMap hpath

/-- Exact radial amplitude-path bridge for a certified fixed-time PDE map. -/
theorem FixedTimePDEBridgeAdapter.radial_bridge
    (A : FixedTimePDEBridgeAdapter X Y EvolvesAt) (d : X)
    (hpath : A.RadialPathAdmissible d) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ A.stateMap (s • d)) d) =
      A.stateMap d - A.stateMap 0 := by
  exact
    radial_flowmap_bridge_of_contDiffOn_open
      (S := A.stateMap) (U := A.admissible) A.admissible_open
      (d := d) A.contDiffOn_stateMap hpath

/--
If the zero datum is a fixed zero state, the radial bridge reconstructs the
endpoint itself rather than only the endpoint difference.
-/
theorem FixedTimePDEBridgeAdapter.radial_bridge_of_zero_fixed
    (A : FixedTimePDEBridgeAdapter X Y EvolvesAt) (d : X)
    (hpath : A.RadialPathAdmissible d)
    (hzero : A.stateMap 0 = 0) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ A.stateMap (s • d)) d) =
      A.stateMap d := by
  calc
    (∫ s in (0 : ℝ)..1, (fderiv ℝ A.stateMap (s • d)) d) =
        A.stateMap d - A.stateMap 0 := A.radial_bridge d hpath
    _ = A.stateMap d := by rw [hzero, sub_zero]

end Adapter

end MNS2
