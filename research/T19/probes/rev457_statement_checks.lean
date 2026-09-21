import NSFormalization.Section3.T19.Density

/-!
# Reviewer 457: non-vacuity and mutation checks

The final equality below is deliberately false while running the negative gate:
changing the headline subcritical threshold from `1 / 2` to `3 / 5` must not be
definitionally accepted as the canonical statement.
-/

noncomputable section

namespace Rev457

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open NSFormalization.Section3.T19
open scoped ENNReal

theorem zero_mem_initialClassT :
    (0 : SpatialField) ∈ initialClassT := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro x i
    rfl
  · intro x
    simp [spatialDivergence, spatialDerivative]

theorem zero_mem_forceClassT :
    (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ht x i
    rfl
  · exact (show tsupport (0 : SpaceTimeField) ⊆
        (∅ : Set ℝ) ×ˢ (Set.univ : Set Space) by simp)

/-- The principal density hypotheses have concrete simultaneous witnesses;
in particular neither the force/initial classes nor the positive-radius and
subcritical parameter ranges are empty. -/
theorem headline_hypotheses_nonempty :
    ∃ a : SpatialField, a ∈ initialClassT ∧
      ∃ g : SpaceTimeField, g ∈ forceClassT ∧
        ∃ ν T s : ℝ, 0 < ν ∧ 0 < T ∧ s < 1 / 2 ∧
          ∃ r : ℝ≥0∞, 0 < r := by
  refine ⟨0, zero_mem_initialClassT, 0, zero_mem_forceClassT, 1, 1, 0, ?_⟩
  norm_num
  exact ⟨1, by norm_num⟩

def widenedPeriodicDensityStatement : Prop :=
  ∀ a : SpatialField, a ∈ initialClassT →
    ∀ ν : ℝ, 0 < ν → ∀ T : ℝ, 0 < T →
      ∀ s : ℝ, s < 3 / 5 →
        RelativelyDenseT 1 s forceClassT (breakdownSetT ν a T)

-- Expected negative check: `rfl` must fail because `3 / 5` is not `1 / 2`.
-- example : widenedPeriodicDensityStatement = periodicDensityStatement := rfl

end Rev457
