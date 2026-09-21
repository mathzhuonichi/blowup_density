import Contracts.V2.LocalTheory
import Contracts.V2.Continuation
import Contracts.V1.TorusLocalTheory

/-!
# P21 Route B targets

These are statement-only research targets in registered contract vocabulary.
They deliberately make no claim about the existing selected high-order
`A01.localHorizon'`.
-/

noncomputable section

namespace BlowupDensity.Research.P21

open Set NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V2.LocalTheory
open BlowupDensity.Contracts.V2.Continuation
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal

/-- Fixed-force whole-space restart, uniform on a smooth H¹ datum ball. -/
def h1RestartR : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), MemForceR f →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassR →
              sobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionR ν a' (timeShift t₀ f) δ,
                  ManuscriptLocalRegularity ν a' (timeShift t₀ f) δ w

/-- Fixed-force periodic restart, uniform on a smooth H¹ datum ball. -/
def h1RestartT : Prop :=
  ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w

/-- Whole-space endpoint consequence of a uniform H¹ bound.  The strict
lifespan inequality is the pressure-gauge-independent registered conclusion. -/
def h1UniformEndpointR : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), MemForceR f →
    ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (a : SpatialField) (u : SpaceTimeField) (p : SpaceTimeScalar),
          a ∈ initialClassR → SolvesBelow ν a f S u p →
            (∀ t ∈ Ico (0 : ℝ) S,
              sobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                ENNReal.ofReal (S + δ) < maximalLifespanR ν a f

/-- Periodic endpoint consequence, with literal velocity and normalized
pressure agreement on the old interval. -/
def h1UniformEndpointT : Prop :=
  ∀ (ν : ℝ), 0 < ν → ∀ (f : SpaceTimeField), f ∈ forceClassT →
    ∀ (S : ℝ), 0 < S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
      ∃ δ : ℝ, 0 < δ ∧
        ∀ (a : SpatialField), a ∈ initialClassT →
          ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
            SolvesBelowT ν a f S u p →
              (∀ t ∈ Ico (0 : ℝ) S,
                periodicSobolevENorm 1 (fun x ↦ u (t, x)) ≤ K) →
                  ∃ v : ClassicalSolutionT ν a f (S + δ),
                    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                      v.velocity (t, x) = u (t, x)) ∧
                    (∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space,
                      v.pressure (t, x) = p (t, x))

end BlowupDensity.Research.P21
