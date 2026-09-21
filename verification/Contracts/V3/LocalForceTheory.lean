import Contracts.V2.Continuation
import Contracts.V2.LocalTheory
import Contracts.V1.TorusLocalTheory

/-! Local existence, uniqueness, maximality and integral continuation beyond
the density force classes. Whole-space forces have smooth Sobolev paths on
the future half-line. Periodic forces are restrictions of smooth periodic
fields on each finite closed future slab, with no negative-time constraint.
Neither branch assumes global time integrability or compact time support. -/
noncomputable section
namespace BlowupDensity.Contracts.V3.LocalForceTheory
open Set MeasureTheory
open NavierStokes.ProblemStatement
open NSFormalization.Paper3 (RealVectorSobolev)
open V1.Data
open scoped ContDiff ENNReal

/-- The whole-space local-theory class, with no half-line `L¹`/`L²` bounds. -/
def SmoothForceR (f : SpaceTimeField) : Prop :=
  ContDiffOn ℝ ∞ f futureDomain ∧
    ∀ m : ℕ, ∃ G : ℝ → RealVectorSobolev (m : ℝ),
      IsSobolevPath (m : ℝ) f G ∧ ContDiffOn ℝ ∞ G futureTimes

/-- Local smoothness of a periodic force by finite closed-slab restrictions. -/
def SmoothForceT (f : SpaceTimeField) : Prop :=
  ∀ S : ℝ, 0 < S → ∃ g : SpaceTimeField,
    ContDiff ℝ ∞ g ∧ V1.TorusData.IsPeriodicOn univ g ∧
      ∀ t ∈ Icc (0 : ℝ) S, ∀ x : Space, g (t, x) = f (t, x)

/-- Independent acceptance statements for both local-theory branches. -/
structure LocalForceTheoryAPI : Prop where
  localR : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, SmoothForceR f →
      ∃ T : ℝ, 0 < T ∧ ∃ w : ClassicalSolutionR ν a f T,
        V2.LocalTheory.ManuscriptLocalRegularity ν a f T w
  maximalR : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, SmoothForceR f →
      ∃ u p, V2.Continuation.IsMaximalSolution ν a f u p
  uniqueR : ∀ ν : ℝ, 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T₁ T₂ : ℝ)
    (w₁ : ClassicalSolutionR ν a f T₁) (w₂ : ClassicalSolutionR ν a f T₂),
      ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
        w₁.velocity (t, x) = w₂.velocity (t, x)
  pressureGaugeR : ∀ ν : ℝ, 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T₁ T₂ : ℝ)
    (w₁ : ClassicalSolutionR ν a f T₁) (w₂ : ClassicalSolutionR ν a f T₂),
      PressureGaugeEquivOn (Ico (0 : ℝ) (min T₁ T₂)) w₁.pressure w₂.pressure
  continuationR : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ initialClassR →
    ∀ f : SpaceTimeField, SmoothForceR f → ∀ S : ℝ, 0 < S →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        V2.Continuation.SolvesBelow ν a f S u p →
        V2.Continuation.squaredHTwoIntegral S u ≠ ⊤ →
          ∃ R : ℝ, S < R ∧ ∃ w : ClassicalSolutionR ν a f R,
            ∀ t ∈ Ico (0 : ℝ) S, ∀ x : Space, w.velocity (t, x) = u (t, x)
  localT : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ V1.TorusLocalTheory.initialClassT →
    ∀ f : SpaceTimeField, SmoothForceT f →
      ∃ T : ℝ, 0 < T ∧ ∃ w : V1.TorusLocalTheory.ClassicalSolutionT ν a f T,
        V1.TorusLocalTheory.PeriodicLocalRegularity ν a f T w
  maximalT : ∀ ν : ℝ, 0 < ν → ∀ a : SpatialField, a ∈ V1.TorusLocalTheory.initialClassT →
    ∀ f : SpaceTimeField, SmoothForceT f →
      ∃ u p, V1.TorusLocalTheory.IsMaximalPeriodicSolution ν a f u p
  uniqueT : ∀ ν : ℝ, 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField) (T₁ T₂ : ℝ)
    (w₁ : V1.TorusLocalTheory.ClassicalSolutionT ν a f T₁)
    (w₂ : V1.TorusLocalTheory.ClassicalSolutionT ν a f T₂),
      ∀ t ∈ Ico (0 : ℝ) (min T₁ T₂), ∀ x : Space,
        w₁.velocity (t, x) = w₂.velocity (t, x) ∧
        w₁.pressure (t, x) = w₂.pressure (t, x)
  continuationT : ∀ ν : ℝ, 0 < ν → ∀ (a : SpatialField) (f : SpaceTimeField),
    SmoothForceT f → ∀ S : ℝ, 0 < S →
      ∀ (u : SpaceTimeField) (p : SpaceTimeScalar),
        V1.TorusLocalTheory.SolvesBelowT ν a f S u p →
        V1.TorusLocalTheory.squaredHTwoIntegralT S u ≠ ⊤ →
          V1.TorusLocalTheory.ExtendsBeyondT ν a f S u p

end BlowupDensity.Contracts.V3.LocalForceTheory
