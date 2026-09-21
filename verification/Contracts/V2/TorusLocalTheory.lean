import Contracts.V1.TorusLocalTheory

/-!
# Periodic local theory V2

This version adds the two fixed-force H¹-uniform statements while reusing all
registered V1 vocabulary.  `T01.torus_local_theory` remains separately
registered for its local theory, H³ continuation, mean-reduction, and
viscosity-rescaling routes.
-/

noncomputable section

namespace BlowupDensity.Contracts.V2.TorusLocalTheory

open Set
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open scoped ENNReal

/-- The periodic H¹-uniform additions to the registered local-theory API. -/
structure PeriodicContinuationH1API : Prop where
  /-- appendix-a-local-theory.tex:146-151 at the H¹ ball, verbatim. -/
  restart : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
      ∀ (S : ℝ), 0 ≤ S → ∀ (K : ℝ≥0∞), K ≠ ⊤ →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ t₀ ∈ Icc (0 : ℝ) S,
            ∀ (a' : SpatialField), a' ∈ initialClassT →
              periodicSobolevENorm 1 a' ≤ K →
                ∃ w : ClassicalSolutionT ν a' (timeShiftT t₀ f) δ,
                  PeriodicLocalRegularity ν a' (timeShiftT t₀ f) δ w

  /-- appendix-a-local-theory.tex:146-153, verbatim, uniform H¹ trajectory
  bound. -/
  restartBeyond : ∀ (ν : ℝ), 0 < ν →
    ∀ (f : SpaceTimeField), f ∈ forceClassT →
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

/-- The V1 periodic local-theory package together with the two H¹-uniform
continuation clauses. -/
def torusLocalTheoryV2Statement : Prop :=
  Nonempty TorusLocalTheoryAPI ∧ PeriodicContinuationH1API

end BlowupDensity.Contracts.V2.TorusLocalTheory
