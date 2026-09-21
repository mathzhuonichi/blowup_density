import Contracts.V2.TorusLocalTheory
import Bindings.TorusLocalTheory
import NSFormalization.Section3.T11.H1RestartBeyond

/-!
# Binding for periodic local theory V2

The V2 statement reuses the complete registered V1 package and adds the two
H¹-uniform fields.  The copied definitions are definitionally equal.  The
distinct classical-solution structures are transported by the established
V1 fieldwise conversions and regularity equivalence.
-/

noncomputable section

namespace BlowupDensity.Bindings

open Set
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Contracts.V1.TorusData
open BlowupDensity.Contracts.V1.TorusLocalTheory
open BlowupDensity.Contracts.V2.TorusLocalTheory
open scoped ENNReal

/-- The two registered periodic H¹-uniform continuation statements. -/
theorem torusContinuationH1API : PeriodicContinuationH1API where
  restart := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, hr⟩ :=
      NSFormalization.Section3.T11.h1RestartT ν hν f hf S hS K hK
    refine ⟨δ, hδ, ?_⟩
    intro t₀ ht₀ a' ha' hbound
    obtain ⟨w, hw⟩ := hr t₀ ht₀ a' ha' hbound
    exact ⟨TorusLocalTheory.toContract w,
      (TorusLocalTheory.periodicLocalRegularity_toContract w).mpr hw⟩
  restartBeyond := by
    intro ν hν f hf S hS K hK
    obtain ⟨δ, hδ, hr⟩ :=
      NSFormalization.Section3.T11.restartBeyondH1T ν hν f hf S hS K hK
    refine ⟨δ, hδ, ?_⟩
    intro a ha u p hsolve hbound
    obtain ⟨v, hu, hp⟩ := hr a ha u p
      ((TorusLocalTheory.solvesBelowT_eq ν a f S u p).mp hsolve) hbound
    exact ⟨TorusLocalTheory.toContract v, hu, hp⟩

/-- The registered V1 package and the two H¹-uniform V2 additions. -/
theorem torusLocalTheoryV2_holds : torusLocalTheoryV2Statement :=
  ⟨⟨torusLocalTheory⟩, torusContinuationH1API⟩

end BlowupDensity.Bindings
