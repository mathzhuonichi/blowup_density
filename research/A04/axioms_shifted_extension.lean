import NSFormalization.Section4.A04.ShiftedExtension
import NSFormalization.Section4.A04.ZeroSolution

open Set
open NSFormalization.Section4
open A02 A04
open scoped ENNReal

#print axioms overlapPaste
#print axioms overlapPaste_left
#print axioms overlapPaste_right
#print axioms contDiffOn_overlap
#print axioms continuousOn_overlap
#print axioms residual_eq_of_local_slices
#print axioms restarted_residual
#print axioms exists_shifted_glue
#print axioms shiftedLocalExtension
#print axioms restartBeyond_of_memForceR'
#print axioms extendsBeyond_of_memForceR'
#print axioms lifespanInfiniteOfLocallyFinite_of_memForceR'

-- The target has exactly lane 215's statement, without a new input.
example : ShiftedLocalExtension := shiftedLocalExtension

-- Exercise the actual gluing branch: old horizon 2, restart at 1, new end 4.
example : Nonempty (ClassicalSolutionR 1 0 0 (1 + 3)) := by
  apply exists_shifted_glue (by norm_num)
    (zeroSol 1 2 (by norm_num) (by norm_num)) (by constructor <;> norm_num)
  · exact zeroSol 1 3 (by norm_num) (by norm_num)
  · norm_num

-- Exercise the lifespan theorem on actual input solutions, not a bare bound.
example : ENNReal.ofReal (1 + 3) ≤ maximalLifespanR 1 0 0 := by
  exact shiftedLocalExtension 1 (by norm_num) 0 0 2
    (zeroSol 1 2 (by norm_num) (by norm_num)) 1 (by constructor <;> norm_num)
    3 (zeroSol 1 3 (by norm_num) (by norm_num))

-- The new endpoint corollary is instantiated by a nonempty solution family.
example : ENNReal.ofReal 1 < maximalLifespanR 1 0 0 := by
  apply extendsBeyond_of_memForceR' 1 0 0 (by norm_num) zero_mem_initialClassR
    memForceR_zero 1 (by norm_num) 0 0
  · intro b hb _
    exact ⟨zeroSol 1 b (by norm_num) hb, rfl, rfl⟩
  · simp [squaredHTwoIntegral, sobolevENorm_eq (D01.isSobolevDatum_zero 2)]
