import Mathlib
import Formal.QuadraticMildNonlinearity

namespace MNS2

open Set MeasureTheory
open scoped Interval

noncomputable section

section QuadraticLinearizedMild

variable {V : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/--
`IsQuadraticLinearizedMildSolutionOn H Q T u h v` is the tangent/variational
mild equation along a supplied base trajectory `u`:

  v(t) = H(t) h - ∫₀ᵗ H(t-s) [Q(u(s),v(s)) + Q(v(s),u(s))] ds.

The implementation uses the already-proved exact Fréchet derivative
`quadraticDerivative Q (u s)` and therefore does not postulate a separate
linearization formula.

This predicate does not assert that `u` itself is a mild solution; use
`IsQuadraticMildTangentPairOn` below when the base PDE semantics are required too.
-/
def IsQuadraticLinearizedMildSolutionOn
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (T : ℝ) (u : ℝ → V) (h : V) (v : ℝ → V) : Prop :=
  0 ≤ T ∧
  ContinuousOn v (Icc (0 : ℝ) T) ∧
  v 0 = h ∧
  ∀ t ∈ Icc (0 : ℝ) T,
    IntervalIntegrable
      (fun s : ℝ => H (t - s) (quadraticDerivative Q (u s) (v s)))
      volume 0 t ∧
    v t =
      H t h -
        ∫ s in (0 : ℝ)..t,
          H (t - s) (quadraticDerivative Q (u s) (v s))

/-- A linearized mild trajectory starts from the tangent datum `h`. -/
theorem quadraticLinearizedMild_initial_value
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    {T : ℝ} {u v : ℝ → V} {h : V}
    (hv : IsQuadraticLinearizedMildSolutionOn H Q T u h v) :
    v 0 = h := by
  exact hv.2.2.1

/-- Recover the linearized Duhamel equation at a certified time. -/
theorem quadraticLinearizedMild_equation_at_time
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    {T : ℝ} {u v : ℝ → V} {h : V}
    (hv : IsQuadraticLinearizedMildSolutionOn H Q T u h v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s : ℝ => H (t - s) (quadraticDerivative Q (u s) (v s)))
      volume 0 t ∧
    v t =
      H t h -
        ∫ s in (0 : ℝ)..t,
          H (t - s) (quadraticDerivative Q (u s) (v s)) := by
  exact hv.2.2.2 t ht

/--
Expanded Navier--Stokes-style bilinear form of the tangent equation.  The equality
`DB(u)[v] = Q u v + Q v u` comes from `quadraticDerivative_apply`.
-/
theorem quadraticLinearizedMild_equation_at_time_expanded
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    {T : ℝ} {u v : ℝ → V} {h : V}
    (hv : IsQuadraticLinearizedMildSolutionOn H Q T u h v)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable
      (fun s : ℝ => H (t - s) (Q (u s) (v s) + Q (v s) (u s)))
      volume 0 t ∧
    v t =
      H t h -
        ∫ s in (0 : ℝ)..t,
          H (t - s) (Q (u s) (v s) + Q (v s) (u s)) := by
  simpa using quadraticLinearizedMild_equation_at_time H Q hv ht

/--
The zero tangent solves the linearized mild equation for zero tangent datum along
any supplied base trajectory, at any nonnegative horizon.
-/
theorem zero_isQuadraticLinearizedMildSolutionOn
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (u : ℝ → V) {T : ℝ} (hT : 0 ≤ T) :
    IsQuadraticLinearizedMildSolutionOn H Q T u 0 (fun _ => 0) := by
  refine ⟨hT, continuousOn_const, rfl, ?_⟩
  intro t ht
  constructor
  · simp
  · simp

/--
A base mild solution together with a tangent trajectory satisfying the exact quadratic
linearized mild equation on the same horizon.
-/
def IsQuadraticMildTangentPairOn
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (T : ℝ) (u₀ h : V) (u v : ℝ → V) : Prop :=
  (MildEvolutionKernel.ofQuadratic H Q).IsMildSolutionOn T u₀ u ∧
  IsQuadraticLinearizedMildSolutionOn H Q T u h v

/--
Existential endpoint semantics for a quadratic mild base trajectory and one tangent
trajectory.  No base-solution or tangent-solution uniqueness is assumed.
-/
def QuadraticMildTangentEvolvesAt
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    (t : ℝ) (u₀ h y : V) : Prop :=
  ∃ u v : ℝ → V,
    IsQuadraticMildTangentPairOn H Q t u₀ h u v ∧
    v t = y

/-- Any endpoint admitted by the tangent relation occurs at nonnegative time. -/
theorem quadraticMildTangentEvolvesAt_nonnegative
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    {t : ℝ} {u₀ h y : V}
    (he : QuadraticMildTangentEvolvesAt H Q t u₀ h y) :
    0 ≤ t := by
  rcases he with ⟨u, v, hp, hy⟩
  exact hp.1.1

/-- At time zero the tangent endpoint is necessarily the tangent initial datum. -/
theorem quadraticMildTangentEvolvesAt_zero_eq_initial
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    {u₀ h y : V}
    (he : QuadraticMildTangentEvolvesAt H Q 0 u₀ h y) :
    y = h := by
  rcases he with ⟨u, v, hp, hy⟩
  calc
    y = v 0 := hy.symm
    _ = h := hp.2.2.2.1

/--
Whenever a base quadratic mild solution exists, the zero tangent endpoint exists for
zero tangent datum.  This is structural only and does not imply uniqueness.
-/
theorem quadraticMildTangent_zero_evolvesAt_zero
    (H : ℝ → V →L[ℝ] V)
    (Q : V →L[ℝ] V →L[ℝ] V)
    {T : ℝ} {u₀ : V} {u : ℝ → V}
    (hu : (MildEvolutionKernel.ofQuadratic H Q).IsMildSolutionOn T u₀ u) :
    QuadraticMildTangentEvolvesAt H Q T u₀ 0 0 := by
  refine ⟨u, (fun _ => 0), ?_, rfl⟩
  exact ⟨hu, zero_isQuadraticLinearizedMildSolutionOn H Q u hu.1⟩

end QuadraticLinearizedMild

end

end MNS2
