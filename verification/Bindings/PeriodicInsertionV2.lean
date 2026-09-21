import Contracts.V2.PeriodicInsertion
import Bindings.PeriodicInsertion
import NSFormalization.Section3.T19.FromData

/-! The raw-data theorem, transported only across the registered solution
structure and its lifespan definition. All geometry and estimates are retained. -/
namespace BlowupDensity.Bindings.PeriodicInsertion

/-- Theorem 3.6 for every prescribed interior coordinate ball. -/
theorem periodicInsertionStatementV2_holds :
    Contracts.V2.PeriodicInsertion.periodicInsertionStatementV2 := by
  intro ν hν center radius hρ hcube a g ha hg T δ hT hδ reference
  obtain ⟨ε₀, hε₀, force, velocity, M, D, C, R, Cpq, Cs,
    hM, hD, hC, hR, hCpq, hCs, hneg, hall⟩ :=
    NSFormalization.Section3.T19.periodicInsertion_from_data
      ν hν center radius hρ hcube a g ha hg T δ hT hδ
      (TorusLocalTheory.ofContract reference)
  refine ⟨ε₀, hε₀, force, velocity, M, D, C, R, Cpq, Cs,
    hM, hD, hC, hR, hCpq, hCs, hneg, ?_⟩
  intro ε hε
  obtain ⟨hf, hdiff, hlife, hsol, hb, hh, hdiv, hsupp, hball, he, hm, hs, hn⟩ := hall ε hε
  refine ⟨hf, hdiff, ?_, ?_, hb, hh, hdiv, hsupp, hball, he, hm, hs, hn⟩
  · rwa [TorusLocalTheory.maximalLifespanT_eq]
  · obtain ⟨w, hw⟩ := hsol
    exact ⟨TorusLocalTheory.toContract w, hw⟩

end BlowupDensity.Bindings.PeriodicInsertion
