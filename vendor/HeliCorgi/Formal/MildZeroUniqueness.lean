import Mathlib
import Formal.MildFlowMapBridge

namespace MNS2

open Set MeasureTheory
open scoped Interval ContDiff

section MildZeroUniqueness

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
Endpoint uniqueness for the existential mild evolution relation at one datum and
one time.  This is a hypothesis interface, not a uniqueness theorem.
-/
def MildEvolutionKernel.EndpointUniqueAt
    (K : MildEvolutionKernel V) (t : ℝ) (u₀ : V) : Prop :=
  ∀ y₁ y₂ : V, K.EvolvesAt t u₀ y₁ → K.EvolvesAt t u₀ y₂ → y₁ = y₂

/--
Trajectory uniqueness on `[0,T]` for one initial datum.  This stronger notion
is useful when a concrete local well-posedness theorem supplies uniqueness of
mild trajectories rather than merely endpoint uniqueness.
-/
def MildEvolutionKernel.TrajectoryUniqueOn
    (K : MildEvolutionKernel V) (T : ℝ) (u₀ : V) : Prop :=
  ∀ u v : ℝ → V,
    K.IsMildSolutionOn T u₀ u →
    K.IsMildSolutionOn T u₀ v →
    ∀ s ∈ Icc (0 : ℝ) T, u s = v s

/-- Trajectory uniqueness implies endpoint uniqueness at the same horizon. -/
theorem MildEvolutionKernel.trajectoryUniqueOn_endpointUniqueAt
    (K : MildEvolutionKernel V) {T : ℝ} {u₀ : V}
    (huniq : K.TrajectoryUniqueOn T u₀) :
    K.EndpointUniqueAt T u₀ := by
  intro y₁ y₂ hy₁ hy₂
  rcases hy₁ with ⟨u, hu, huy₁⟩
  rcases hy₂ with ⟨v, hv, hvy₂⟩
  have hT : T ∈ Icc (0 : ℝ) T := ⟨hu.1, le_rfl⟩
  calc
    y₁ = u T := huy₁.symm
    _ = v T := huniq u v hu hv T hT
    _ = y₂ := hvy₂

/--
If the abstract nonlinearity vanishes at zero, the constant zero trajectory is
a mild solution on every nonnegative horizon.

For a concrete incompressible Navier--Stokes specialization, proving the
projected quadratic term vanishes at zero should discharge `hB0`.
-/
theorem MildEvolutionKernel.zero_isMildSolutionOn
    (K : MildEvolutionKernel V) {T : ℝ}
    (hT : 0 ≤ T) (hB0 : K.nonlinearity 0 = 0) :
    K.IsMildSolutionOn T 0 (fun _ : ℝ => (0 : V)) := by
  refine ⟨hT, ?_, rfl, ?_⟩
  · exact continuous_const.continuousOn
  · intro t ht
    constructor
    · simp [hB0]
    · simp [hB0]

/-- Zero therefore belongs to the existential endpoint relation at any nonnegative time. -/
theorem MildEvolutionKernel.zero_evolvesAt_zero
    (K : MildEvolutionKernel V) {T : ℝ}
    (hT : 0 ≤ T) (hB0 : K.nonlinearity 0 = 0) :
    K.EvolvesAt T 0 0 := by
  refine ⟨fun _ : ℝ => (0 : V), K.zero_isMildSolutionOn hT hB0, ?_⟩
  rfl

/--
A certified state map selects the zero endpoint if zero data are admissible,
the mild nonlinearity vanishes at zero, and the mild endpoint is unique for
zero data at the selected time.

No uniqueness is inferred from the existential `EvolvesAt` predicate itself.
-/
theorem NavierStokesTimeBridgeAdapter.stateMap_zero_of_mild_endpointUnique
    (K : MildEvolutionKernel V)
    (A : NavierStokesTimeBridgeAdapter V V
      (fun t x y => K.EvolvesAt t x y))
    (t : ℝ) (ht : t ∈ A.certifiedTimes)
    (hzero_admissible : (0 : V) ∈ A.admissible t)
    (hB0 : K.nonlinearity 0 = 0)
    (huniq : K.EndpointUniqueAt t 0) :
    A.stateMap t 0 = 0 := by
  have hselected : K.EvolvesAt t 0 (A.stateMap t 0) :=
    A.realizesNS t ht 0 hzero_admissible
  have hzero : K.EvolvesAt t 0 0 :=
    K.zero_evolvesAt_zero (A.certified_time_nonnegative ht) hB0
  exact huniq (A.stateMap t 0) 0 hselected hzero

/--
Version using trajectory uniqueness, which is converted to endpoint uniqueness
before selecting the zero endpoint.
-/
theorem NavierStokesTimeBridgeAdapter.stateMap_zero_of_mild_trajectoryUnique
    (K : MildEvolutionKernel V)
    (A : NavierStokesTimeBridgeAdapter V V
      (fun t x y => K.EvolvesAt t x y))
    (t : ℝ) (ht : t ∈ A.certifiedTimes)
    (hzero_admissible : (0 : V) ∈ A.admissible t)
    (hB0 : K.nonlinearity 0 = 0)
    (huniq : K.TrajectoryUniqueOn t 0) :
    A.stateMap t 0 = 0 := by
  exact A.stateMap_zero_of_mild_endpointUnique K t ht hzero_admissible hB0
    (K.trajectoryUniqueOn_endpointUniqueAt huniq)

/--
The radial flow-map / Duhamel identity with the zero-fixed condition discharged
by endpoint uniqueness rather than supplied as an independent assumption.
-/
theorem NavierStokesTimeBridgeAdapter.radial_bridge_eq_mild_duhamel_of_endpointUnique
    (K : MildEvolutionKernel V)
    (A : NavierStokesTimeBridgeAdapter V V
      (fun t x y => K.EvolvesAt t x y))
    (t : ℝ) (ht : t ∈ A.certifiedTimes) (d : V)
    (hpath : MapsTo (fun a : ℝ => a • d) (uIcc (0 : ℝ) 1) (A.admissible t))
    (hzero_admissible : (0 : V) ∈ A.admissible t)
    (hB0 : K.nonlinearity 0 = 0)
    (huniq : K.EndpointUniqueAt t 0) :
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
  have hzero : A.stateMap t 0 = 0 :=
    A.stateMap_zero_of_mild_endpointUnique K t ht hzero_admissible hB0 huniq
  exact A.radial_bridge_eq_mild_duhamel K t ht d hpath hzero

end MildZeroUniqueness

end MNS2
