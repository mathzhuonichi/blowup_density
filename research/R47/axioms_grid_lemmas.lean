import Bindings.GridLemmas

/-!
Transitive-axiom audit and non-vacuity probes for lane 247.

Each printed theorem must report exactly
`[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings

#print axioms exists_ball_in_common_cell
#print axioms gridObservation_locality

/-! The common-ball theorem fires for a genuinely nonempty one-grid family and
produces a positive-radius ball contained in one of its registered cells. -/
example (grid : Grid) (x : Space) :
    ∃ x₀ r, 0 < r ∧ ∀ _i : Fin 1, ∃ k,
      Metric.ball x₀ r ⊆ grid.cell k := by
  simpa using exists_ball_in_common_cell 1 (fun _ => grid) x

/-! The locality hypotheses are simultaneously inhabited.  In particular,
the totalized integral causes no hidden obstruction for the zero field. -/
example (grid : Grid) (k₀ : Fin 3 → ℤ) :
    gridObservation grid (fun _ => 0) =
      gridObservation grid (fun _ => 0) := by
  apply gridObservation_locality grid (fun _ => 0) (fun _ => 0)
    ∅ k₀
  · simp
  · exact empty_subset _
  · simp
  · simp
  · simp
