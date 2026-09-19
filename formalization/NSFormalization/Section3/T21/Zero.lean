import NSFormalization.Section3.T21.Definitions
import NSFormalization.Section3.T19.Bookkeeping
import NSFormalization.Section3.T20.CriticalEnergy

/-!
# T21 N4, N5, and N12: zero force and zero initial datum
-/

noncomputable section

namespace NSFormalization.Section3.T21

open Set
open NavierStokes.ProblemStatement
open NSFormalization.Section4.A02 (SpatialField SpaceTimeField)
open NSFormalization.Section3.T10
open scoped ContDiff ENNReal

/-- N4: the zero spacetime field is an admissible periodic force. -/
theorem zero_mem_forceClassT : (0 : SpaceTimeField) ∈ forceClassT := by
  refine ⟨contDiff_const, ?_, ∅, isCompact_empty, empty_subset _, ?_⟩
  · intro t _ht x j
    rfl
  · rw [tsupport_zero]
    exact empty_subset _

/-- N5's norm helper, specialized from the canonical T19 supplier. -/
theorem forceSobolevENormT_zero (q : ℝ≥0∞) (s : ℝ) :
    forceSobolevENormT q s (0 : SpaceTimeField) = 0 :=
  NSFormalization.Section3.T19.torusForceSobolevENorm_zero q s

/-- N5: the zero force belongs to every critical ball of positive radius. -/
theorem zeroMemBall (c : ℝ) (hc : 0 < c) : ∀ ν : ℝ, 0 < ν → ∀ s : ℝ,
    (0 : SpaceTimeField) ∈ criticalBallT c ν s := by
  intro ν hν s
  refine ⟨zero_mem_forceClassT, ?_⟩
  rw [forceSobolevENormT_zero]
  exact ENNReal.ofReal_pos.mpr (mul_pos hc hν)

/-- N12: the zero spatial field is an admissible periodic initial datum. -/
theorem zeroInitialClass : (fun _ : Space ↦ 0) ∈ initialClassT :=
  NSFormalization.Section3.T20.zero_mem_initialClassT

end NSFormalization.Section3.T21
