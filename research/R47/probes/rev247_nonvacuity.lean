import Bindings.GridLemmas
import NSFormalization.Paper3.CellIntegrability

noncomputable section

open Set MeasureTheory
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3
open BlowupDensity.Contracts.V1.Data
open BlowupDensity.Bindings

private def unitGrid : Grid where
  offset := fun _ => 0
  width := fun _ => 1
  width_pos := by simp

private def shiftedGrid : Grid where
  offset := fun _ => 1 / 3
  width := fun _ => 2
  width_pos := by simp

/- Two genuinely different prescribed grids still receive one common
positive-radius ball. -/
example (x : Space) :
    ∃ x₀ r, 0 < r ∧ ∀ i : Fin 2, ∃ k,
      Metric.ball x₀ r ⊆ (![unitGrid, shiftedGrid] i).cell k := by
  simpa using exists_ball_in_common_cell 2 ![unitGrid, shiftedGrid] x

/- The locality hypotheses are inhabited by nonzero observed fields, not only
by the all-zero field used in the lane audit. -/
example (grid : Grid) (k₀ : Fin 3 → ℤ) (e : Space) (he : e ≠ 0) :
    (fun _ : Space => e) 0 ≠ 0 ∧
      gridObservation grid (fun _ => e) = gridObservation grid (fun _ => e) := by
  constructor
  · simpa using he
  · apply gridObservation_locality grid (fun _ => e) (fun _ => e) ∅ k₀
    · simp
    · exact empty_subset _
    · obtain ⟨K, hK, hsub⟩ := grid.cell_subset_compact k₀
      exact (continuous_const.continuousOn.integrableOn_compact hK).mono_set hsub
    · obtain ⟨K, hK, hsub⟩ := grid.cell_subset_compact k₀
      exact (continuous_const.continuousOn.integrableOn_compact hK).mono_set hsub
    · simp
