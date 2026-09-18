import Contracts.V1.ConservativeForcing
import Bindings.ConservativeForcing
import TestSupport.Axioms

/-! Public-type, specification-field conformance, non-vacuity, and
transitive-axiom checks for `T04.conservative_forcing` V1. -/

noncomputable section

namespace BlowupDensity.Tests

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-- The implementation supplies both clauses of `prop:conservative`. -/
theorem checkedConservativeForcing : Contracts.V1.ConservativeForcingAPI :=
  Bindings.conservativeForcing

run_cmd TestSupport.checkAxioms ``checkedConservativeForcing

/-! ## Independent conformance with both fields of `research/T24/Spec.lean` -/

example :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0 :=
  checkedConservativeForcing.potential_pairing

example :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0 :=
  checkedConservativeForcing.zero_from_rest

/-! ## Genuine non-vacuity at the zero potential -/

example : PeriodicPotentialT (0 : SpaceTimeScalar) := by
  constructor
  · exact contDiff_const
  · exact fun _ _ _ _ ↦ rfl

example : conservativeForceT (0 : SpaceTimeScalar) = 0 := by
  funext z
  simp [conservativeForceT, pressureGradient]

/-- A contract-side classical solution really inhabits the quantifier in both
API clauses; it has zero velocity and zero pressure, not merely a zero
integrand detached from the PDE solution structure. -/
example (ν : ℝ) (T : ℝ) (hT : 0 < T) :
    ∃ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT 0) T,
      S.velocity = 0 ∧ S.pressure = 0 :=
  ⟨Bindings.ConservativeForcing.restSolution ν T hT, rfl, rfl⟩

end BlowupDensity.Tests
