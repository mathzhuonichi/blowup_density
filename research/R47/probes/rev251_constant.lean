import Bindings.ForceCellIntegral
noncomputable section
namespace BlowupDensity.Bindings
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Contracts.V1 Contracts.V1.Data
open NSFormalization.Paper3
variable {ν : ℝ} {P : PacketAPI ν} (A : InsertionFamilyAPI ν P)
-- Mutate only the claimed mean from zero to one; retain every hypothesis and proof.
theorem rev251_mutated_component {ε t : ℝ}
    (hε : ε ∈ Ioc 0 A.ε₀) (ht : t ∈ Ico 0 A.T)
    (grid : Grid) (k₀ : Fin 3 → ℤ) (hB : A.ball ⊆ grid.cell k₀) (j : Fin 3) :
    (∫ x in grid.cell k₀, (A.velocity ε (t,x) - A.v (t,x)) j) = 1 := by
  apply setIntegral_component_eq_zero
    ((velocityDifference_slice_smooth A hε ht).of_le (by simp))
    (velocityDifference_slice_compact A hε ht)
  · intro x
    exact (NavierStokes.ComparatorBridge.divergence_eq
      (fun z => A.velocity ε z - A.v z) t x) ▸ A.velocityDifference_divFree ε hε t ht x
  · exact grid.measurableSet_cell k₀
  · exact (subset_tsupport _).trans ((A.velocityDifference_support ε hε t ht).trans hB)


end BlowupDensity.Bindings
