import NSFormalization.Paper1.PeriodicLifespan

/-!
# The admissible periodic initial-data class

Paper 1, equation `eq:inputspaces`, fixes the space
`C^infinity_div(T^3; R^3)`.  Its Euclidean lifts are smooth, unit-periodic,
and divergence free.  No zero-mean condition is imposed.  An actual `Flow`
already enforces every one of these conditions at time zero; the results
below extract them from its existing fields without a local-existence premise.
-/

noncomputable section
open Set
open scoped ContDiff BigOperators

namespace NSFormalization.Paper1.PeriodicInitialData
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration

/-- The lifted manuscript initial-data space. -/
structure IsAdmissibleInitialData (a : Space → Space) : Prop where
  smooth : ContDiff ℝ ∞ a
  periodic : UnitPeriods a
  divergence_free : ∀ x : Space,
    (∑ i : Fin 3, (fderiv ℝ a x (coordinateVector i)) i) = 0

end NSFormalization.Paper1.PeriodicInitialData

namespace NSFormalization.Paper1.PeriodicLifespan
open NavierStokes.ProblemStatement NavierStokes.PeriodicIntegration
open NSFormalization.Paper1.PeriodicInitialData

/-- The spatial initial slice is smooth even though spacetime smoothness is
only assumed on the one-sided time slab. -/
theorem Flow.initial_smooth {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) : ContDiff ℝ ∞ a := by
  have hzero : (0 : ℝ) ∈ Ico 0 S := ⟨le_rfl, W.horizon_pos⟩
  have hs : ContDiff ℝ ∞ (fun x : Space => W.velocity (0, x)) := by
    apply contDiffOn_univ.mp
    exact W.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨hzero, mem_univ x⟩)
  simpa only [W.initial] using hs

theorem Flow.initial_periodic {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) : UnitPeriods a := by
  intro x i
  simpa only [W.initial] using
    W.velocity_periodic 0 ⟨le_rfl, W.horizon_pos⟩ x i

theorem Flow.initial_divergence_free
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) (x : Space) :
    (∑ i : Fin 3, (fderiv ℝ a x (coordinateVector i)) i) = 0 := by
  have hd := W.divergence 0 ⟨le_rfl, W.horizon_pos⟩ x
  simpa only [spatialDivergence, spatialDerivative, W.initial] using hd

/-- Any genuine positive-horizon flow certifies that its initial datum lies
in the manuscript's smooth divergence-free periodic class. -/
theorem Flow.initial_admissible
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (W : Flow ν a f S) : IsAdmissibleInitialData a :=
  ⟨W.initial_smooth, W.initial_periodic, W.initial_divergence_free⟩

/-- Initial-data admissibility is necessary for every actual flow witness,
independently of viscosity and forcing. -/
theorem isEmpty_flow_of_not_admissible
    {ν S : ℝ} {a : Space → Space} {f : VelocityField}
    (ha : ¬ IsAdmissibleInitialData a) : IsEmpty (Flow ν a f S) :=
  ⟨fun W => ha W.initial_admissible⟩

end NSFormalization.Paper1.PeriodicLifespan
