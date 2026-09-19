import NSFormalization.Section3.T19.DensityEngine

namespace NSFormalization.Section3.T19

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpaceTimeField)
open NSFormalization.Section3.T10

private theorem review_zero_mem_initialClassT :
    (fun _ : Space ↦ (0 : Space)) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x j
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

private theorem review_zero_mem_forceClassT :
    (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro t _ht x i
    rfl
  · exact ⟨∅, isCompact_empty, empty_subset _, by simp⟩

-- All quantified side conditions have concrete witnesses, and the conclusion
-- produces an actual member of the breakdown set.
example :
    (breakdownSetT (1 : ℝ) (fun _ : Space ↦ (0 : Space)) 1).Nonempty := by
  obtain ⟨f, hf, _hclose⟩ :=
    fixedInitialDensity (fun _ : Space ↦ (0 : Space)) review_zero_mem_initialClassT
      1 (by norm_num) 1 (by norm_num) 0 (by norm_num)
      (0 : SpaceTimeField) review_zero_mem_forceClassT 1 (by norm_num)
  exact ⟨f, hf⟩

end NSFormalization.Section3.T19
