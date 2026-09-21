import Mathlib
import Formal.PDEBridgeAdapter

namespace MNS2

open Set
open scoped Interval ContDiff

/--
A time-indexed interface for attaching the abstract flow-map bridge to
Navier--Stokes semantics.

`NSEvolvesAt t x y` is supplied by a later PDE-specific layer and is intended
to mean that `y` is the Navier--Stokes state at time `t` evolved from initial
datum `x`. This file does not define the Navier--Stokes equations or prove
existence, uniqueness, regularity, or differentiable dependence.

The structure records only the time slices for which a genuine state map,
an open admissible data domain, `C¹` dependence, and semantic realization have
already been certified.
-/
structure NavierStokesTimeBridgeAdapter
    (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (NSEvolvesAt : ℝ → X → Y → Prop) where
  certifiedTimes : Set ℝ
  certifiedTimes_nonneg : ∀ t ∈ certifiedTimes, 0 ≤ t
  stateMap : ℝ → X → Y
  admissible : ℝ → Set X
  admissible_open : ∀ t ∈ certifiedTimes, IsOpen (admissible t)
  contDiffOn_stateMap :
    ∀ t ∈ certifiedTimes, ContDiffOn ℝ 1 (stateMap t) (admissible t)
  realizesNS :
    ∀ t ∈ certifiedTimes, ∀ x ∈ admissible t,
      NSEvolvesAt t x (stateMap t x)

section NavierStokesTimeBridge

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {NSEvolvesAt : ℝ → X → Y → Prop}

/--
Extract the already-certified fixed-time PDE adapter at a certified time.
-/
def NavierStokesTimeBridgeAdapter.atTime
    (A : NavierStokesTimeBridgeAdapter X Y NSEvolvesAt)
    (t : ℝ) (ht : t ∈ A.certifiedTimes) :
    FixedTimePDEBridgeAdapter X Y (NSEvolvesAt t) where
  stateMap := A.stateMap t
  admissible := A.admissible t
  admissible_open := A.admissible_open t ht
  contDiffOn_stateMap := A.contDiffOn_stateMap t ht
  realizesPDE := A.realizesNS t ht

/-- Every certified time is nonnegative. -/
theorem NavierStokesTimeBridgeAdapter.certified_time_nonnegative
    (A : NavierStokesTimeBridgeAdapter X Y NSEvolvesAt)
    {t : ℝ} (ht : t ∈ A.certifiedTimes) : 0 ≤ t := by
  exact A.certifiedTimes_nonneg t ht

/--
Every point on a certified affine data path realizes the supplied
Navier--Stokes evolution relation at the selected time.
-/
theorem NavierStokesTimeBridgeAdapter.affine_path_realizesNS
    (A : NavierStokesTimeBridgeAdapter X Y NSEvolvesAt)
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (x d : X)
    (hpath : MapsTo (fun s : ℝ => x + s • d) (uIcc (0 : ℝ) 1) (A.admissible t))
    {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) 1) :
    NSEvolvesAt t (x + s • d) (A.stateMap t (x + s • d)) := by
  exact A.realizesNS t ht (x + s • d) (hpath hs)

/--
Exact affine bridge at a certified Navier--Stokes time slice.
The tangent is the fixed, unnormalized direction `d`.
-/
theorem NavierStokesTimeBridgeAdapter.affine_bridge_at_time
    (A : NavierStokesTimeBridgeAdapter X Y NSEvolvesAt)
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (x d : X)
    (hpath : MapsTo (fun s : ℝ => x + s • d) (uIcc (0 : ℝ) 1) (A.admissible t)) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ (A.stateMap t) (x + s • d)) d) =
      A.stateMap t (x + d) - A.stateMap t x := by
  exact (A.atTime t ht).affine_bridge x d hpath

/-- Exact radial amplitude-path bridge at a certified time slice. -/
theorem NavierStokesTimeBridgeAdapter.radial_bridge_at_time
    (A : NavierStokesTimeBridgeAdapter X Y NSEvolvesAt)
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (d : X)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) (A.admissible t)) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ (A.stateMap t) (s • d)) d) =
      A.stateMap t d - A.stateMap t 0 := by
  exact (A.atTime t ht).radial_bridge d hpath

/--
If the zero datum is known to evolve to the zero state at the selected time,
the radial bridge reconstructs the endpoint state itself.
-/
theorem NavierStokesTimeBridgeAdapter.radial_bridge_at_time_of_zero_fixed
    (A : NavierStokesTimeBridgeAdapter X Y NSEvolvesAt)
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (d : X)
    (hpath : MapsTo (fun s : ℝ => s • d) (uIcc (0 : ℝ) 1) (A.admissible t))
    (hzero : A.stateMap t 0 = 0) :
    (∫ s in (0 : ℝ)..1, (fderiv ℝ (A.stateMap t) (s • d)) d) =
      A.stateMap t d := by
  exact (A.atTime t ht).radial_bridge_of_zero_fixed d hpath hzero

end NavierStokesTimeBridge

end MNS2
