import Contracts.V1.ConservativeForcing
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T24.ConservativeAssembly

/-!
# Binding for the conservative-forcing contract

The two contract-local definitions are checked against the canonical T24
definitions by `rfl`.  The contract and canonical `ClassicalSolutionT`
structures are distinct inductive types, so each quantified solution is
transported with the fieldwise conversion already registered by
`Bindings.TorusLocalTheory`; in particular, velocity is preserved by `rfl`.
-/

noncomputable section

namespace BlowupDensity.Bindings.ConservativeForcing

open Set MeasureTheory
open NavierStokes.ProblemStatement
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V1
open scoped ContDiff ENNReal BigOperators RealInnerProductSpace

/-! ## Definitional drift guards -/

theorem periodicPotentialT_eq (φ : SpaceTimeScalar) :
    Contracts.V1.PeriodicPotentialT φ =
      NSFormalization.Section3.T24.PeriodicPotentialT φ := rfl

theorem conservativeForceT_eq (φ : SpaceTimeScalar) :
    Contracts.V1.conservativeForceT φ =
      NSFormalization.Section3.T24.conservativeForceT φ := rfl

/-! ## Fieldwise transport of the two clauses -/

theorem potential_pairing :
    ∀ (ν : ℝ) (T : ℝ), 0 < T → ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
      ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
        ∀ t ∈ Ico (0 : ℝ) T,
          ∫ y : PeriodicTorus,
              torusLift (fun x : Space ↦
                (inner ℝ (conservativeForceT φ (t, x)) (S.velocity (t, x)) : ℝ))
                y ∂periodicTorusMeasure = 0 := by
  intro ν T hT φ hφ S t ht
  exact NSFormalization.Section3.T24.potential_pairing
    ν T hT φ hφ (TorusLocalTheory.ofContract S) t ht

theorem zero_from_rest :
    ∀ (ν : ℝ), 0 < ν → ∀ (T : ℝ), 0 < T →
      ∀ φ : SpaceTimeScalar, PeriodicPotentialT φ →
        ∀ S : ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT φ) T,
          ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Space, S.velocity (t, x) = 0 := by
  intro ν hν T hT φ hφ S t ht x
  exact NSFormalization.Section3.T24.zero_from_rest
    ν hν T hT φ hφ (TorusLocalTheory.ofContract S) t ht x

/-- The registered two-field conservative-forcing API. -/
theorem conservativeForcing : Contracts.V1.ConservativeForcingAPI where
  potential_pairing := potential_pairing
  zero_from_rest := zero_from_rest

/-- The registered statement alias is inhabited. -/
theorem conservativeForcingStatement_holds :
    Contracts.V1.conservativeForcingStatement :=
  conservativeForcing

/-- Contract-side genuine rest solution, obtained by the established
fieldwise conversion from the canonical witness. -/
def restSolution (ν : ℝ) (T : ℝ) (hT : 0 < T) :
    ClassicalSolutionT ν (0 : SpatialField) (conservativeForceT 0) T :=
  TorusLocalTheory.toContract
    (NSFormalization.Section3.T24.restSolution ν T hT)

end BlowupDensity.Bindings.ConservativeForcing

namespace BlowupDensity.Bindings

/-- Public registered conservative-forcing API. -/
theorem conservativeForcing : Contracts.V1.ConservativeForcingAPI :=
  ConservativeForcing.conservativeForcing

/-- Public proof of the statement alias. -/
theorem conservativeForcingStatement_holds :
    Contracts.V1.conservativeForcingStatement :=
  ConservativeForcing.conservativeForcingStatement_holds

end BlowupDensity.Bindings
