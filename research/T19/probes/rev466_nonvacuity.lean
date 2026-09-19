import NSFormalization.Section3.T19.Projection

namespace NSFormalization.Section3.T19.Review466

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ENNReal

private theorem zero_initial_mem : (0 : SpatialField) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

private theorem zero_force_mem : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ht x i
    rfl
  · exact (show tsupport (0 : SpaceTimeField) ⊆
        (∅ : Set ℝ) ×ˢ (Set.univ : Set Space) by simp)

/-- A concrete positive-parameter instance: the produced fibre is genuinely nonempty. -/
example :
    ∃ f : SpaceTimeField,
      ((0 : SpatialField), f) ∈ extendedBreakdownSetT 1 1 ∧
        forceSobolevENormT 1 0 (fun z => f z - (0 : SpaceTimeField) z) < 1 := by
  exact extendedProductDensity 1 (by norm_num) 1 (by norm_num)
    0 (by norm_num) 0 zero_initial_mem 0 zero_force_mem 1 (by norm_num)

end NSFormalization.Section3.T19.Review466
