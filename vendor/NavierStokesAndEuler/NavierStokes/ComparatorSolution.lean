import NavierStokes.ComparatorR3Theorem
import NavierStokes.ComparatorTheorem

/-!
# Navier–Stokes Comparator submission: options (C) and (D)

Expose the project's proof adapters under the reference theorem names.
The adapters import `ComparatorDefinitions`, never the challenge module.
-/

namespace NavierStokes.Comparator

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- (C) Breakdown of Navier–Stokes solutions on ℝ³. -/
theorem navier_stokes_breakdown_R3 (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessRn nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_R3 nu hnu

/-- (D) Breakdown of Navier–Stokes solutions on ℝ³/ℤ³. -/
theorem navier_stokes_breakdown_periodic (nu : ℝ) (hnu : nu > 0) :
    ∃ (u₀ : ℝ³ → ℝ³) (f : ℝ³ → ℝ → ℝ³),
    InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic f ∧
    ¬ (∃ v p, NavierStokesExistenceAndSmoothnessPeriodic nu u₀ f v p) := by
  exact ComparatorBridge.navier_stokes_breakdown_periodic nu hnu

end NavierStokes.Comparator

#print axioms NavierStokes.Comparator.navier_stokes_breakdown_R3
#print axioms NavierStokes.Comparator.navier_stokes_breakdown_periodic
