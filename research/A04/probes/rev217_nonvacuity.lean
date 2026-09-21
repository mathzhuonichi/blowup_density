import NSFormalization.Section4.A04.ShiftedExtension
import NSFormalization.Section4.A04.ZeroSolution

open Set
open NSFormalization.Section4
open A02 A04

-- The strict gluing branch is inhabited, with a nonempty overlap `[1, 2)`.
example : Nonempty (ClassicalSolutionR 1 0 0 (1 + 3)) := by
  apply exists_shifted_glue (by norm_num)
    (zeroSol 1 2 (by norm_num) (by norm_num)) (by constructor <;> norm_num)
  · exact zeroSol 1 3 (by norm_num) (by norm_num)
  · norm_num
