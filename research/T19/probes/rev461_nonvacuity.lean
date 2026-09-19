import NSFormalization.Section3.T19.Threading
import NSFormalization.Section3.T24.ConservativeAssembly

noncomputable section

namespace Rev461

open Set NavierStokes.ProblemStatement
open NSFormalization.Section3.T10 NSFormalization.Section3.T18
open NSFormalization.Section3.T19 NSFormalization.Section3.T24
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)

theorem zero_mem_initialClassT : (0 : SpatialField) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

theorem zero_mem_forceClassT : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ht x i
    rfl
  · exact (show tsupport (0 : SpaceTimeField) ⊆
      (∅ : Set ℝ) ×ˢ (univ : Set Space) by simp)

/-- Concrete simultaneous witnesses for all inputs to the insertion constructor. -/
example : Nonempty (Σ data : InsertionData, PeriodicInsertionAPI data) := by
  have hforce : conservativeForceT 0 = (0 : SpaceTimeField) := by
    funext z
    simp [conservativeForceT, pressureGradient]
  let reference₀ : ClassicalSolutionT (1 : ℝ) (0 : SpatialField)
      (conservativeForceT 0) ((1 : ℝ) + 1) := restSolution 1 (1 + 1) (by norm_num)
  let reference : ClassicalSolutionT (1 : ℝ) (0 : SpatialField)
      (0 : SpaceTimeField) ((1 : ℝ) + 1) := hforce ▸ reference₀
  have ha : (0 : SpatialField) ∈ initialClassT := zero_mem_initialClassT
  have hg : (0 : SpaceTimeField) ∈ forceClassT := zero_mem_forceClassT
  let data := insertionData (by norm_num : (0 : ℝ) < 1) ha hg
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) reference
  exact ⟨⟨data, insertion (by norm_num : (0 : ℝ) < 1) ha hg
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1) reference⟩⟩

end Rev461
