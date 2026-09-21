import Contracts.V2.ConservativeForcing
import Bindings.ConservativeForcing
import Bindings.BoundaryInsertion
import NSFormalization.Section3.T24.ConservativeOmega

/-! Fieldwise transport over the registered bounded-domain solution record. -/
noncomputable section
namespace BlowupDensity.Bindings.ConservativeForcingV2
open Contracts.V2.ConservativeForcing

/-- Definitional guard for the physical force. -/
theorem conservativeForceOmega_eq (φ : Contracts.V1.Data.SpaceTimeScalar) :
    conservativeForceOmega φ = NSFormalization.Section3.T24.conservativeForceOmega φ := rfl

/-- Both bounded-domain clauses, without additional force-class assumptions. -/
theorem conservativeForcingOmega : ConservativeForcingOmegaAPI where
  potential_pairing := by
    intro ν T hT Ω hΩ φ hφ S t ht
    exact NSFormalization.Section3.T24.conservativeForcingOmega.potential_pairing
      ν T hT Ω hΩ φ hφ (BoundaryInsertion.Contract.solutionTo S) t ht
  zero_from_rest := by
    intro ν hν T hT Ω hΩ φ hφ S t ht x hx
    exact NSFormalization.Section3.T24.conservativeForcingOmega.zero_from_rest
      ν hν T hT Ω hΩ φ hφ (BoundaryInsertion.Contract.solutionTo S) t ht x hx

/-- Proposition 3.17 on the torus and on bounded no-slip domains. -/
theorem conservativeForcingStatementV2_holds : conservativeForcingStatementV2 :=
  ⟨ConservativeForcing.conservativeForcing, conservativeForcingOmega⟩

end BlowupDensity.Bindings.ConservativeForcingV2
