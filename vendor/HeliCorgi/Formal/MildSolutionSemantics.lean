import Mathlib

namespace MNS2

open Set MeasureTheory
open scoped Interval

/--
Abstract data for a Banach-valued mild evolution equation

  u(t) = H(t) u₀ - ∫₀ᵗ H(t-s) B(u(s)) ds.

For Navier--Stokes, a later semantic layer is intended to instantiate `H` with
the Stokes/heat evolution `exp(ν t Δ)` on a chosen divergence-free state space
and `B` with the projected quadratic convection operator
`P div (u ⊗ u)`.

This structure deliberately does not assert that those concrete operators have
already been constructed or that a solution exists.  It only fixes the shape
of the mild equation used by the semantic predicate below.
-/
structure MildEvolutionKernel
    (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] where
  linearEvolution : ℝ → V →L[ℝ] V
  nonlinearity : V → V

section MildSolution

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
`IsMildSolutionOn K T u₀ u` means that `u` is a continuous trajectory on
`[0,T]`, starts from `u₀`, and satisfies the Banach-valued Duhamel formula at
every time in that interval.  Interval integrability is carried explicitly so
the integral equation is not satisfied merely through the default value of a
non-integrable Bochner integral.
-/
def MildEvolutionKernel.IsMildSolutionOn
    (K : MildEvolutionKernel V) (T : ℝ) (u₀ : V) (u : ℝ → V) : Prop :=
  0 ≤ T ∧
  ContinuousOn u (Icc (0 : ℝ) T) ∧
  u 0 = u₀ ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    IntervalIntegrable
      (fun s : ℝ => K.linearEvolution (t - s) (K.nonlinearity (u s)))
      volume 0 t ∧
    u t =
      K.linearEvolution t u₀ -
        ∫ s in (0 : ℝ)..t,
          K.linearEvolution (t - s) (K.nonlinearity (u s))

/--
Endpoint evolution relation induced by the mild equation.  This is existential:
it does not assert uniqueness of the witnessing trajectory.
-/
def MildEvolutionKernel.EvolvesAt
    (K : MildEvolutionKernel V) (t : ℝ) (u₀ y : V) : Prop :=
  ∃ u : ℝ → V, K.IsMildSolutionOn t u₀ u ∧ u t = y

/-- Any endpoint admitted by the mild relation occurs at a nonnegative time. -/
theorem MildEvolutionKernel.evolvesAt_nonnegative
    (K : MildEvolutionKernel V) {t : ℝ} {u₀ y : V}
    (h : K.EvolvesAt t u₀ y) : 0 ≤ t := by
  rcases h with ⟨u, hu, _⟩
  exact hu.1

/-- A mild trajectory starts from the datum named in the predicate. -/
theorem MildEvolutionKernel.initial_value
    (K : MildEvolutionKernel V) {T : ℝ} {u₀ : V} {u : ℝ → V}
    (h : K.IsMildSolutionOn T u₀ u) : u 0 = u₀ := by
  exact h.2.2.1

/-- Recover the Duhamel equation and integrability at any certified time. -/
theorem MildEvolutionKernel.equation_at_time
    (K : MildEvolutionKernel V) {T : ℝ} {u₀ : V} {u : ℝ → V}
    (h : K.IsMildSolutionOn T u₀ u)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s : ℝ => K.linearEvolution (t - s) (K.nonlinearity (u s)))
      volume 0 t ∧
    u t =
      K.linearEvolution t u₀ -
        ∫ s in (0 : ℝ)..t,
          K.linearEvolution (t - s) (K.nonlinearity (u s)) := by
  exact h.2.2.2 t ht

/--
At time zero the endpoint of the mild evolution relation is necessarily the
initial datum.  This uses only the explicit initial-value clause and does not
assert uniqueness at positive times.
-/
theorem MildEvolutionKernel.evolvesAt_zero_eq_initial
    (K : MildEvolutionKernel V) {u₀ y : V}
    (h : K.EvolvesAt 0 u₀ y) : y = u₀ := by
  rcases h with ⟨u, hu, huy⟩
  calc
    y = u 0 := huy.symm
    _ = u₀ := hu.2.2.1

/--
Expose a witness trajectory together with the actual endpoint Duhamel formula.
This is the semantic fact needed later when `EvolvesAt` is attached to the
time-indexed flow-map bridge.
-/
theorem MildEvolutionKernel.evolvesAt_endpoint_equation
    (K : MildEvolutionKernel V) {t : ℝ} {u₀ y : V}
    (h : K.EvolvesAt t u₀ y) :
    ∃ u : ℝ → V,
      K.IsMildSolutionOn t u₀ u ∧
      IntervalIntegrable
        (fun s : ℝ => K.linearEvolution (t - s) (K.nonlinearity (u s)))
        volume 0 t ∧
      y =
        K.linearEvolution t u₀ -
          ∫ s in (0 : ℝ)..t,
            K.linearEvolution (t - s) (K.nonlinearity (u s)) := by
  rcases h with ⟨u, hu, huy⟩
  have ht : t ∈ Icc (0 : ℝ) t := ⟨hu.1, le_rfl⟩
  have heq := K.equation_at_time hu ht
  refine ⟨u, hu, heq.1, ?_⟩
  calc
    y = u t := huy.symm
    _ =
        K.linearEvolution t u₀ -
          ∫ s in (0 : ℝ)..t,
            K.linearEvolution (t - s) (K.nonlinearity (u s)) := heq.2

end MildSolution

end MNS2
