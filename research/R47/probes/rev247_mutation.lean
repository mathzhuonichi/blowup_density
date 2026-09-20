import Bindings.GridLemmas

noncomputable section

namespace BlowupDensity.Review247

open Set
open NavierStokes.ProblemStatement (Space)
open NSFormalization.Paper3
open Contracts.V1.Data

/- Intentional negative mutation: double the asserted radius but retain the
original proof, which supplies containment only for radius `r`. -/
theorem exists_ball_in_common_cell_mutated
    (n : ℕ) (grids : Fin n → Grid) (_x : Space) :
    ∃ x₀ r, 0 < r ∧ ∀ i, ∃ k,
      Metric.ball x₀ (2 * r) ⊆ (grids i).cell k := by
  obtain ⟨x₀, r, hr, indices, hball⟩ := finite_grids_common_ball grids
  refine ⟨x₀, r, hr, fun i => ⟨indices i, ?_⟩⟩
  exact (hball i).trans ((grids i).cellInterior_subset_cell (indices i))

end BlowupDensity.Review247
