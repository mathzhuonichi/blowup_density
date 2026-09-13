/-
Copyright 2026 The Formal Conjectures Authors.

This file has been modified from its original form in the Formal Conjectures
project.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib

/-!
# Comparator challenge: unforced Euler breakdown on ℝ³

Adapted from `FormalConjectures/Millenium/NavierStokes.lean` at
https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/Millenium/NavierStokes.lean

This is the whole-space breakdown alternative specialized to zero viscosity
and zero external force. It retains the source's initial-data decay, joint
smoothness, square integrability, and uniform energy conditions. Velocity and
pressure take position before time. The time derivative at zero is taken
within `[0,∞)`.

All problem-specific definitions are included here. The reference imports only
Mathlib, independently of the Euler proof development. The theorem proofs are
intentional Comparator challenge placeholders.
-/


-- Inline the only needed notation from FormalConjecturesForMathlib.Geometry.3d.
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open ContDiff Set InnerProductSpace MeasureTheory

namespace Euler

/-- The divergence of a vector field, computed as the trace of its derivative. -/
noncomputable def divergence (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  (fderiv ℝ v x).trace ℝ ℝ³

local notation "∇⬝" => divergence

/-- Smooth, divergence-free initial velocity. -/
structure InitialVelocityCondition (u₀ : ℝ³ → ℝ³) : Prop where
  div_free : ∀ x, ∇⬝ u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

/-- Every spatial derivative of the initial velocity decays faster than any polynomial. -/
structure InitialVelocityConditionDecay (u₀ : ℝ³ → ℝ³) : Prop extends
    InitialVelocityCondition u₀ where
  decay : ∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x,
    ‖iteratedFDeriv ℝ m u₀ x‖ ≤ C / (1 + ‖x‖) ^ K

/-- A global smooth solution of unforced incompressible Euler on ℝ³. -/
structure EulerExistenceAndSmoothness
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  /-- `∂ₜv + (v · ∇)v = -∇p`: viscosity and external force are both zero. -/
  euler : ∀ x, ∀ t ≥ 0,
    derivWithin (v x ·) (Set.Ici 0) t + fderiv ℝ (v · t) x (v x t) =
      -gradient (p · t) x
  div_free : ∀ x, ∀ t ≥ 0, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry v) (Set.univ ×ˢ Set.Ici 0)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry p) (Set.univ ×ˢ Set.Ici 0)

/-- The whole-space solution class, retaining the source's finite, uniformly bounded energy. -/
structure EulerExistenceAndSmoothnessR3
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop
    extends EulerExistenceAndSmoothness u₀ v p where
  integrable : ∀ t ≥ 0, MemLp (‖v · t‖) 2
  globally_bounded_energy : ∃ E : ℝ, ∀ t ≥ 0, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E

/-- Some admissible initial velocity has no global smooth unforced Euler solution
in the whole-space energy class above. This is the theorem to supply to Comparator. -/
theorem euler_breakdown_R3 :
    ∃ u₀ : ℝ³ → ℝ³, InitialVelocityConditionDecay u₀ ∧
      ¬ (∃ v p, EulerExistenceAndSmoothnessR3 u₀ v p) := by
  sorry

/-!
## Finite lifespan and quantitative singularity

The following version of `EulerPacketInduction.exists_compact_smooth_euler_singularity`
uses ordinary velocity and pressure functions, with position before time as above.
Its finite-interval solution class matches the original theorem: the velocity and
its strong time derivative have continuous L² spatial jets of every order.
Pressure is spatially differentiable at interior times; no time regularity or
normalization is imposed on it.

This is a separate solution class from the global challenge. Maximality below is
asserted in this all-order Sobolev class. The last clause independently retains
nonexistence in the broader global class `EulerExistenceAndSmoothnessR3`.

The spatial suprema take values in `ℝ≥0∞`, so an unbounded field has norm `⊤`.
The theorem separately requires bounded C¹ norms and a finite vorticity integral
on every shorter closed time interval, locating the singularity at the endpoint.
-/

open scoped ENNReal Topology

/-- The L² equivalence class of a square-integrable function. The fallback makes
this a total function; the solution conditions require square integrability
wherever it is used. -/
noncomputable def toL2 {V : Type*} [NormedAddCommGroup V] (f : ℝ³ → V) :
    Lp V 2 (volume : Measure ℝ³) := by
  classical
  exact if h : MemLp f 2 volume then h.toLp f else 0

/-- A spatially smooth path whose actual spatial derivative tensors belong to L²
and depend continuously on time in L², at every finite order. -/
structure SobolevSmoothOn (I : Set ℝ) (v : ℝ³ → ℝ → ℝ³) : Prop where
  spatial_smooth : ∀ t ∈ I, ContDiff ℝ ∞ (v · t)
  integrable : ∀ t ∈ I, MemLp (v · t) 2
  jets_integrable : ∀ m : ℕ, ∀ t ∈ I, MemLp (iteratedFDeriv ℝ m (v · t)) 2
  continuous : ContinuousOn (fun t => toL2 (v · t)) I
  jets_continuous : ∀ m : ℕ,
    ContinuousOn (fun t => toL2 (iteratedFDeriv ℝ m (v · t))) I

/-- Scalar-pressure Euler on a time set `I` in the original theorem's smooth
Sobolev class. The velocity and its strong time derivative have continuous L²
spatial jets of every order. The Euler equation uses this derivative witness.

As in `IsSmoothScalarEuler`, the time law and scalar-pressure equation are
required at interior times. There is no endpoint derivative condition. We use
`Ico 0 T` for a maximal lifespan and `Icc 0 T` for a closed interval. -/
structure EulerSobolevExistenceAndSmoothnessR3On (I : Set ℝ)
    (u₀ : ℝ³ → ℝ³) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ) : Prop where
  div_free : ∀ x, ∀ t ∈ I, ∇⬝ (v · t) x = 0
  initial_condition : ∀ x, v x 0 = u₀ x
  velocity_smooth : SobolevSmoothOn I v
  pressure_differentiable : ∀ t ∈ interior I, Differentiable ℝ (p · t)
  euler : ∃ w : ℝ³ → ℝ → ℝ³,
    SobolevSmoothOn I w ∧
      (∀ t ∈ interior I,
        HasDerivAt (fun s => toL2 (v · s)) (toL2 (w · t)) t) ∧
      (∀ x, ∀ t ∈ interior I,
        w x t + fderiv ℝ (v · t) x (v x t) = -gradient (p · t) x)

/-- The ordinary curl of a velocity field, expressed through its spatial derivative.
Indices in `Fin 3` are cyclic. -/
noncomputable def vorticity (v : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    (fderiv ℝ v x (EuclideanSpace.single (i + 1) 1)) (i + 2) -
      (fderiv ℝ v x (EuclideanSpace.single (i + 2) 1)) (i + 1))

/-- The sum of the spatial suprema of the velocity norm and derivative operator norm. -/
noncomputable def velocityC1Norm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  (⨆ x, ENNReal.ofReal ‖v x‖) + (⨆ x, ENNReal.ofReal ‖fderiv ℝ v x‖)

/-- The spatial supremum of the Euclidean norm of the actual vorticity. -/
noncomputable def vorticityNorm (v : ℝ³ → ℝ³) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ‖vorticity v x‖

/-- Nonzero, compactly supported, rapidly decaying initial data have one smooth
finite-energy Euler solution on a positive finite maximal lifespan `[0,T*)`.
Closed-interval solutions in the all-order Sobolev class exist exactly below `T*`.
The chosen solution has locally bounded C¹ norm and locally finite vorticity
integral, but its C¹ upper limit and full vorticity integral are infinite at `T*`.
The same datum also satisfies the global breakdown conclusion above. -/
theorem exists_compact_smooth_euler_singularity :
    ∃ (u₀ : ℝ³ → ℝ³) (Tstar : ℝ) (v : ℝ³ → ℝ → ℝ³) (p : ℝ³ → ℝ → ℝ),
      InitialVelocityConditionDecay u₀ ∧ HasCompactSupport u₀ ∧ u₀ ≠ 0 ∧
      0 < Tstar ∧ Tstar ≤ 1 ∧
      EulerSobolevExistenceAndSmoothnessR3On (Ico 0 Tstar) u₀ v p ∧
      (∃ E : ℝ, ∀ t ∈ Ico (0 : ℝ) Tstar, (∫ x : ℝ³, ‖v x t‖ ^ 2) < E) ∧
      (∀ T : ℝ, 0 < T →
        ((∃ w q, EulerSobolevExistenceAndSmoothnessR3On (Icc 0 T) u₀ w q) ↔ T < Tstar)) ∧
      (∀ T ∈ Ioo 0 Tstar,
        (⨆ t ∈ Icc (0 : ℝ) T, velocityC1Norm (v · t)) < ⊤ ∧
        (∫⁻ t in Ico (0 : ℝ) T, vorticityNorm (v · t)) < ⊤) ∧
      Filter.limsup (fun t : ℝ => velocityC1Norm (v · t)) (𝓝[<] Tstar) = ⊤ ∧
      (∫⁻ t in Ico (0 : ℝ) Tstar, vorticityNorm (v · t)) = ⊤ ∧
      ¬ (∃ w q, EulerExistenceAndSmoothnessR3 u₀ w q) := by
  sorry

end Euler
