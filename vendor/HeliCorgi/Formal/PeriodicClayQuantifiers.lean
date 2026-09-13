import Formal.PeriodicClayCore
import Mathlib.Tactic

/-!
Logical quantifier facts around the independently defined periodic unforced Clay-B proposition.

This file is repo-authored during integration because the uploaded Astra bundle contained the
compiled `ClayQuantifiers.olean` and verification record, but not the corresponding
`ClayQuantifiers.lean` source. The statements below match the documented theorem roles while
remaining ordinary kernel-checked Lean source.
-/

noncomputable section
set_option autoImplicit false

namespace ClayNS

/-- Failure of the universal periodic alternative is exactly the existence of one positive-viscosity
admissible datum for which no global solution in the declared class exists. -/
theorem not_clayB_iff_unforcedPeriodicObstruction :
    ¬ ClayB ↔
      ∃ ν : ℝ, 0 < ν ∧
        ∃ u₀ : Point → Point, AdmissiblePeriodicDatum u₀ ∧
          ¬ ∃ u : Velocity, ∃ p : Pressure, GlobalPeriodicSolution ν u₀ u p := by
  constructor
  · intro hB
    by_contra hobs
    apply hB
    intro ν hν u₀ hu₀
    by_contra hsol
    apply hobs
    exact ⟨ν, hν, u₀, hu₀, hsol⟩
  · rintro ⟨ν, hν, u₀, hu₀, hsol⟩ hB
    exact hsol (hB ν hν u₀ hu₀)

/-- Any obstruction to periodic alternative B must use a nonzero datum, because the zero datum has
the explicit zero global solution. -/
theorem failure_of_clayB_has_nonzero_datum (hB : ¬ ClayB) :
    ∃ ν : ℝ, 0 < ν ∧
      ∃ u₀ : Point → Point, AdmissiblePeriodicDatum u₀ ∧
        u₀ ≠ (fun _ _ => 0) ∧
        ¬ ∃ u : Velocity, ∃ p : Pressure, GlobalPeriodicSolution ν u₀ u p := by
  obtain ⟨ν, hν, u₀, hu₀, hsol⟩ :=
    not_clayB_iff_unforcedPeriodicObstruction.mp hB
  refine ⟨ν, hν, u₀, hu₀, ?_, hsol⟩
  intro hzero
  apply hsol
  rw [hzero]
  exact ⟨(fun _ _ _ => 0), (fun _ _ => 0), zero_global_periodic ν⟩

/-- A solved parameter family proves the universal periodic alternative only when every admissible
datum is explicitly covered by that family. Coverage is a hypothesis, not a property of shear
data proved in this development. -/
theorem covering_solved_family_implies_clayB
    {ι : Type*}
    (datum : ι → Point → Point)
    (solved : ∀ ν : ℝ, 0 < ν → ∀ i : ι,
      ∃ u : Velocity, ∃ p : Pressure, GlobalPeriodicSolution ν (datum i) u p)
    (covers : ∀ u₀ : Point → Point, AdmissiblePeriodicDatum u₀ →
      ∃ i : ι, datum i = u₀) :
    ClayB := by
  intro ν hν u₀ hu₀
  obtain ⟨i, hi⟩ := covers u₀ hu₀
  obtain ⟨u, p, hsol⟩ := solved ν hν i
  rw [← hi]
  exact ⟨u, p, hsol⟩

#print axioms not_clayB_iff_unforcedPeriodicObstruction
#print axioms failure_of_clayB_has_nonzero_datum
#print axioms covering_solved_family_implies_clayB

end ClayNS
