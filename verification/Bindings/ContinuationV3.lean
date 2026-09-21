import Contracts.V3.Continuation
import Bindings.ContinuationV2
import Bindings.LocalTheoryV2
import NSFormalization.Section4.A04.H1RestartBeyond

/-!
# Binding for A04 continuation V3

The implementation and contract copy the datum, force, time-shift and Sobolev
definitions token-for-token.  Their `ClassicalSolutionR` structures are
distinct, so the restart witness and `SolvesBelow` premise use the established
fieldwise conversions from the V2 bindings.  The maximal-lifespan conclusion
uses the established `iSup` bridge.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V2.LocalTheory
open BlowupDensity.Contracts.V2.Continuation
open BlowupDensity.Contracts.V3.Continuation
open scoped ENNReal

/-- The registered H¹ restart and strict endpoint continuation statements. -/
theorem continuationV3_holds : ContinuationV3API where
  restartH1 := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, hr⟩ :=
      NSFormalization.Section4.A04.h1RestartR ν hν f hf S hS K hK
    refine ⟨δ, hδ, ?_⟩
    intro t₀ ht₀ a' ha' hbound
    obtain ⟨w, hw⟩ := hr t₀ ht₀ a' ha' hbound
    exact ⟨maximalPartial_ofA02 w, localTheoryV2_regularity_ofA02 hw⟩
  restartBeyondH1 := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, hr⟩ :=
      NSFormalization.Section4.A04.restartBeyondH1 ν hν f hf S hS K hK
    refine ⟨δ, hδ, ?_⟩
    intro a u p ha hu hbound
    rw [← maximalPartial_maximalLifespanR_eq]
    exact hr a u p ha
      ((continuationV2_solvesBelow_iff ν a f S u p).mp hu) hbound

end BlowupDensity.Bindings
