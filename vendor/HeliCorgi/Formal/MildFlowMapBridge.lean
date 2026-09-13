import Mathlib
import Formal.NavierStokesTimeBridge
import Formal.MildSolutionSemantics

namespace MNS2

open Set MeasureTheory
open scoped Interval ContDiff

section MildFlowMapBridge

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
At every admissible datum of a certified time slice whose semantic relation is
`K.EvolvesAt`, the selected state-map endpoint has an actual mild trajectory
witness satisfying the Duhamel equation.

This theorem does not manufacture the certified slice.  In particular, the
existence of `A` still carries the open-domain, `C¹`, and semantic-realization
obligations from `NavierStokesTimeBridgeAdapter`.
-/
theorem NavierStokesTimeBridgeAdapter.mild_endpoint_equation
    (K : MildEvolutionKernel V)
    (A : NavierStokesTimeBridgeAdapter V V
      (fun t x y => K.EvolvesAt t x y))
    (t : ℝ) (ht : t ∈ A.certifiedTimes)
    (x : V) (hx : x ∈ A.admissible t) :
    ∃ u : ℝ → V,
      K.IsMildSolutionOn t x u ∧
      IntervalIntegrable
        (fun s : ℝ => K.linearEvolution (t - s) (K.nonlinearity (u s)))
        volume 0 t ∧
      A.stateMap t x =
        K.linearEvolution t x -
          ∫ s in (0 : ℝ)..t,
            K.linearEvolution (t - s) (K.nonlinearity (u s)) := by
  have hrel : K.EvolvesAt t x (A.stateMap t x) :=
    A.realizesNS t ht x hx
  exact K.evolvesAt_endpoint_equation hrel

/--
Every point on a certified radial initial-data path has a mild trajectory
witness ending at the state selected by the certified flow map.
-/
theorem NavierStokesTimeBridgeAdapter.radial_path_has_mild_witness
    (K : MildEvolutionKernel V)
    (A : NavierStokesTimeBridgeAdapter V V
      (fun t x y => K.EvolvesAt t x y))
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (d : V)
    (hpath : MapsTo (fun a : ℝ => a • d) (uIcc (0 : ℝ) 1) (A.admissible t))
    {a : ℝ} (ha : a ∈ uIcc (0 : ℝ) 1) :
    ∃ u : ℝ → V,
      K.IsMildSolutionOn t (a • d) u ∧
      u t = A.stateMap t (a • d) := by
  have hrel : K.EvolvesAt t (a • d) (A.stateMap t (a • d)) :=
    A.realizesNS t ht (a • d) (hpath ha)
  exact hrel

/--
Conditional equality between the exact radial flow-map path integral and the
mild Duhamel endpoint selected by the same certified time slice.

The extra `hzero` hypothesis is intentional.  `K.EvolvesAt` is existential and
may be non-single-valued, so zero data are not silently assumed to select the
zero endpoint.  A later concrete Navier--Stokes uniqueness/zero-solution layer
may discharge this hypothesis.
-/
theorem NavierStokesTimeBridgeAdapter.radial_bridge_eq_mild_duhamel
    (K : MildEvolutionKernel V)
    (A : NavierStokesTimeBridgeAdapter V V
      (fun t x y => K.EvolvesAt t x y))
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (d : V)
    (hpath : MapsTo (fun a : ℝ => a • d) (uIcc (0 : ℝ) 1) (A.admissible t))
    (hzero : A.stateMap t 0 = 0) :
    ∃ u : ℝ → V,
      K.IsMildSolutionOn t d u ∧
      IntervalIntegrable
        (fun s : ℝ => K.linearEvolution (t - s) (K.nonlinearity (u s)))
        volume 0 t ∧
      (∫ a in (0 : ℝ)..1,
          (fderiv ℝ (A.stateMap t) (a • d)) d) =
        K.linearEvolution t d -
          ∫ s in (0 : ℝ)..t,
            K.linearEvolution (t - s) (K.nonlinearity (u s)) := by
  have h_one : (1 : ℝ) ∈ uIcc (0 : ℝ) 1 := by
    norm_num [uIcc]
  have hd : d ∈ A.admissible t := by
    have := hpath h_one
    simpa using this
  rcases A.mild_endpoint_equation K t ht d hd with ⟨u, hu, hint, hend⟩
  refine ⟨u, hu, hint, ?_⟩
  calc
    (∫ a in (0 : ℝ)..1,
        (fderiv ℝ (A.stateMap t) (a • d)) d) =
        A.stateMap t d :=
      A.radial_bridge_at_time_of_zero_fixed t ht d hpath hzero
    _ =
        K.linearEvolution t d -
          ∫ s in (0 : ℝ)..t,
            K.linearEvolution (t - s) (K.nonlinearity (u s)) := hend

end MildFlowMapBridge

end MNS2
