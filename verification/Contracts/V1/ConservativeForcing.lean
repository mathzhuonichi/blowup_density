import Contracts.V1.TorusLocalTheory

/-!
# Contract: conservative forcing on the three-torus

This is the reconciled T24c statement of `prop:conservative`
(`paper/sections/03-torus.tex:723-740`).  It uses the registered T10/T11
solution vocabulary from `Contracts.V1.TorusLocalTheory`.

## Scope

The paper's bounded-domain branch with homogeneous no-slip
(`03-torus.tex:724-725`) is deliberately omitted: no bounded-domain/no-slip
carrier is registered in V1.  This contract states only the torus branch.

## Restatement provenance

`PeriodicPotentialT`, `conservativeForceT`, `ConservativeForcingAPI`, and
`conservativeForcingStatement` are restated token-for-token from
`research/T24/Spec.lean:1360-1417`.  The binding guards both definitions by
`rfl`.  `ClassicalSolutionT` is not restated here; this module reuses the
registered contract structure, and the binding transports it fieldwise through
`Bindings.TorusLocalTheory.ofContract`.
-/

noncomputable section

namespace BlowupDensity.Contracts.V1

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-- `03-torus.tex:723-726`: the conservative potential class — a globally
defined smooth scalar `φ` on spacetime, unit-periodic in every spatial
coordinate.  Periodicity excludes the affine (non-periodic) gauges the paper
sets aside. -/
def PeriodicPotentialT (φ : SpaceTimeScalar) : Prop :=
  ContDiff ℝ ∞ φ ∧ IsPeriodicOn univ φ

/-- `03-torus.tex:723-726`: the conservative force `f = -∇φ`, in the registered
pressure-gradient token. -/
def conservativeForceT (φ : SpaceTimeScalar) : SpaceTimeField :=
  fun z ↦ -pressureGradient φ z.1 z.2

/-- Proposition `prop:conservative` (`paper/sections/03-torus.tex:723-740`) on
the torus.  `Prop`-valued: two universal implications choosing no witness or
constant.

The paper's bounded-domain branch with homogeneous no-slip (`03-torus.tex:724-725`)
is deliberately omitted: no bounded-domain / no-slip carrier exists in the tree,
so only the torus branch is stated — out of V1 scope. -/
structure ConservativeForcingAPI : Prop where
  /-- `03-torus.tex:729-731`: the displayed pairing `∫_{T³} f·u = -∫∇φ·u = 0`
  at every time of the classical lifespan, for every smooth periodic `φ` and
  every solution `S` from rest with force `-∇φ`.
  Exact quantifier order: `∀ ν`, `∀ T`, `0<T`, `∀ φ`, `PeriodicPotentialT φ`,
  `∀ S`, `∀ t ∈ Ico 0 T`.
  Non-vacuity: constrains the Haar integral of the explicit inner product
  `⟪-∇φ(t), u(t)⟫` to be `0`; it holds only through incompressibility and
  periodicity of `u`, hence a genuine integration-by-parts claim, not `True`. -/
  potential_pairing :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0
  /-- `03-torus.tex:723-728,732-737`: from rest, a conservative torus force
  yields only the zero solution on its classical lifespan — `u ≡ 0` on `[0,T)`
  (corrected from a global `u = 0`, which is false off the slab that
  `ClassicalSolutionT` constrains).
  Exact quantifier order: `∀ ν`, `0<ν`, `∀ T`, `0<T`, `∀ φ`,
  `PeriodicPotentialT φ`, `∀ S`, `∀ t ∈ Ico 0 T`, `∀ x`.
  Non-vacuity: pins the velocity of every such solution to `0` on the whole
  lifespan; it follows from `potential_pairing` and the classical energy
  identity, so it constrains real solution data. -/
  zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0

/-- `03-torus.tex:723-740`: the statement form of `prop:conservative` (already a
`Prop`; introducing this alias asserts nothing). -/
def conservativeForcingStatement : Prop := ConservativeForcingAPI

end BlowupDensity.Contracts.V1
